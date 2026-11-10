-- Prove2me | Theorems.Thm_SeededShannon_theorem_6_13
-- name    : SeededShannon.theorem_6_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:45.047652+00:00
-- url     : https://prove2.me/theorems/ddfc4b12-89a5-4952-a355-d0b9e67dcfe9
-- title:
--   Theorem 6.13 — iO, one-way functions and strongly robust PRCs give list-decodable seeded codes at rate $1-H(p)-\varepsilon$
-- statement:
--   Fix constants $0<p<r<1/2$ and $0<\varepsilon<1-H(p)$, where $H$ is the binary entropy function in bits. Assume
--
--   1. indistinguishability obfuscation for polynomial-size circuits;
--   2. one-way functions;
--   3. a zero-bit public-key pseudorandom code (Definition 3.5) with strong $r$-robustness, negligible soundness error and codeword length $\mathrm{poly}(\lambda)$.
--
--   Then there are a binary seeded code $\Pi=(\mathrm{Setup},\mathrm{Encode},\mathrm{Decode})$, a polynomial minimum message length $k_{\min}(\lambda)$ and a polynomial list bound $L(\lambda,k)$ such that, on all message lengths $k_{\min}(\lambda)\le k\le 2^\lambda$,
--
--   1. the algorithms run in time $\mathrm{poly}(\lambda,k)$ (for polynomially bounded $k$), and codewords have length $N(\lambda,k)$;
--   2. $\Pi$ has list size $L$ and is $p$-sound;
--   3. $\Pi$ is selectively $(p,L)$-correct (Definition 3.15);
--   4. the rate satisfies
--   $$\frac{k}{N(\lambda,k)}\ \ge\ 1-H(p)-\varepsilon .$$
--
--   This is the first plain-model seeded code at Shannon capacity $1-H(p)$ against computationally bounded channels; the code is Construction 6.1.
--
--   **Formalization Note** iO is the published `NoisyOWMPC.IOScheme.IsIO`, one-way functions `NoisyOWMPC.OWFExists`, $H$ the published `WildeQIT.binaryEntropy`.
--
--   Differences from the source:
--   - encoding: iO security against samplers Samp outputting (C₀, C₁, st) that agree everywhere with probability 1 − negl (Def. 3.1) → NoisyOWMPC.IOScheme.IsIO: fixed polynomial-size sequences (C₀,λ, C₁,λ, z_λ) of always-equivalent circuits; reason: equivalent: a nonuniform sampler can output a fixed triple, and conversely the best equivalent triple in a sampler's support bounds its advantage up to the negligible non-equivalence probability
--   - reading: a family of polynomial-size circuits, the two circuits of a pair of unspecified sizes → the two circuits of a pair have equal size and equal output length; reason: with unequal sizes no obfuscator can exist (the size is visible), so the hypothesis would be vacuous; the paper pads its circuits to common size (p.38)
--   - encoding: an efficient obfuscator with functionality preservation → IsIO also carries a public polynomial bound `len` on the obfuscated description and output-length preservation; reason: both follow from polynomial running time and functionality preservation
--   - reading: efficient / polynomial-time adversaries → nonuniform polynomial-size deterministic circuit families (`Distinguisher`, `CircFamily`); schemes are uniform machines; reason: Def. 3.1 allows non-uniform adversaries and the reductions hard-wire keys, so one nonuniform class is used throughout; a randomized adversary is matched by its best coins
--   - encoding: A₁ sends x* and retains a state st; A₂(st, crs) sends y → a fixed message sequence x*_λ of polynomially bounded length; st hard-wired into the circuit family A₂ run on (1^λ, crs); reason: deterministic nonuniform adversaries
--   - reading: has rate 1 − H(p) − ε → k / N(λ, k) ≥ 1 − H(p) − ε at every supported (λ, k); reason: Lemma 6.2 proves 'at least'; k/N is rational, so equality is impossible in general
--   - encoding: polynomial minimum message length k_min(λ) and polynomial list bound L(λ, k) → polynomially bounded k_min and L; reason: raising k_min to its polynomial bound shrinks the supported set and a larger L is still a list bound, so the two are equivalent
--   - reading: Construction 6.1 admits an instantiation as a binary seeded code → there exists a seeded code with the stated properties; reason: the identity of the witness is not a property of the code; the claim about Construction 6.1 itself is Theorem 6.4
--   - reading: for every crs and y (list size, p-soundness) → for every seed Setup outputs at a supported length and every y ∈ {0,1}^N; reason: Definition 3.15 types Encode and Decode on seeds
--   - reading: a PRC satisfying Definition 3.5 → IsEfficient ∧ Pseudorandom of the PRC; reason: Definition 3.5 is the efficient syntax plus the pseudorandomness property
--   - encoding: algorithms running in time poly(λ, k) for every polynomially bounded k → fixed machines, with a time exponent per polynomially bounded length function; reason: literal; for polynomially bounded k, poly(λ, k) is poly(λ)
--   - encoding: Decode outputs a set T; malformed or unsupported values make the experiment output 0 → Decode outputs a list whose length is bounded by L; y of the wrong length or an unsupported |x*| makes the experiment output 0; reason: conventions of p.22
--   - encoding: H, the binary entropy function → WildeQIT.binaryEntropy, logarithm base 2; reason: same function
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 6.13, p.47 (PDF p.50)

import Mathlib
import Definitions.Def_NoisyOWMPC_IOScheme
import Definitions.Def_NoisyOWMPC_OWFExists
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_SeededShannon_ZeroBitPRC
import Definitions.Def_SeededShannon_SeededCode

set_option autoImplicit false

namespace SeededShannon

open NoisyOWMPC

/-- **Theorem 6.13 (List-decodable seeded codes at Shannon rate)** (Dujmovic, Lu, Silbak, Wichs,
*Shannon Rate Seeded Codes from Indistinguishability Obfuscation*, STOC 2027 submission
(manuscript sha256 52f4b606…a769709), Theorem 6.13, p.47): fix `0 < p < r < 1/2` and
`0 < ε < 1 − H(p)`. Assume indistinguishability obfuscation for polynomial-size circuits, one-way
functions, and a zero-bit public-key pseudorandom code (Definition 3.5) with strong `r`-robustness,
negligible soundness error and codeword length `poly(λ)`. Then there are a binary seeded code, a
polynomial minimum message length `k_min(λ)` and a polynomial list bound `L(λ, k)` such that on all
lengths `k_min(λ) ≤ k ≤ 2^λ` the code is selectively `(p, L)`-correct and `p`-sound, has algorithms
running in time `poly(λ, k)`, and has rate at least `1 − H(p) − ε`.

**Formalization Note** `H` is the binary entropy in bits (the published `WildeQIT.binaryEntropy`).
iO is the published `NoisyOWMPC.IOScheme.IsIO` (fixed sequences of equal-size equivalent circuits
in place of samplers, a public description-length bound), one-way functions are
`NoisyOWMPC.OWFExists`. Adversaries are nonuniform polynomial-size circuit families; schemes are
uniform machines. "Construction 6.1 admits an instantiation" is read as the existence of the code;
the rate "`1 − H(p) − ε`" is read as a lower bound `k / N(λ, k) ≥ 1 − H(p) − ε`. -/
theorem theorem_6_13 (p r ε : ℝ) (hp : 0 < p) (hpr : p < r) (hr : r < 1 / 2) (hε : 0 < ε)
    (hεH : ε < 1 - WildeQIT.binaryEntropy p)
    (hiO : ∃ O : IOScheme, O.IsIO) (hOWF : OWFExists)
    (hPRC : ∃ P : ZeroBitPRC, P.IsEfficient ∧ P.Pseudorandom ∧ P.StronglyRobust r ∧
      P.NegligiblySound ∧ PolyBounded P.n) :
    ∃ (C : SeededCode) (kmin : ℕ → ℕ) (L : ℕ → ℕ → ℕ),
      PolyBounded kmin ∧ PolyBounded₂ L ∧
      C.IsEfficient (fun lam k => kmin lam ≤ k ∧ k ≤ 2 ^ lam) ∧
      C.EncodeLength (fun lam k => kmin lam ≤ k ∧ k ≤ 2 ^ lam) ∧
      C.ListBound (fun lam k => kmin lam ≤ k ∧ k ≤ 2 ^ lam) L ∧
      C.Sound (fun lam k => kmin lam ≤ k ∧ k ≤ 2 ^ lam) p ∧
      C.SelectivelyCorrect (fun lam k => kmin lam ≤ k ∧ k ≤ 2 ^ lam) p ∧
      ∀ lam k, kmin lam ≤ k → k ≤ 2 ^ lam →
        1 - WildeQIT.binaryEntropy p - ε ≤ (k : ℝ) / C.N lam k := by sorry

end SeededShannon
