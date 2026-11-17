-- Prove2me | Theorems.Thm_SYKCavity_Supplement_theorem_26
-- name    : SYKCavity.Supplement.theorem_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:48:27.497554+00:00
-- url     : https://prove2.me/theorems/a83e52f8-cfb7-4c23-b7c9-7a91c704f6c4
-- title:
--   Theorem 26 — Ising mixtures of orders $\ge3$ below $\beta^*$: $\langle\sigma_A\rangle$ to $N^{-c}$ and $\log Z_N$ to $N^{-c}$ in $N^C$ bit operations
-- statement:
--   Fix the mixture in (7.1): a nonempty finite set $P$ of interaction orders, all at least $3$, and coefficients $\lambda_p>0$. Fix an inverse temperature $0\le\beta<\beta^*$, where $\beta^*$ is the static transition. Fix an observable degree $\ell\ge0$ and exponents $a,c>0$. Then there is a deterministic classical algorithm that outputs $\hat m_A(\beta,J)$ for every $A\subseteq[N]$ with $|A|\le\ell$, and $\hat L(\beta,J)$, such that for all sufficiently large $N$
--   $$\Pr_J\Big[\sum_{|A|\le\ell}|\hat m_A-\langle\sigma_A\rangle_{\beta,J}|^2>N^{-2c}\ \text{ or }\ |\hat L-\log Z_N(\beta,J)|>N^{-c}\Big]\le N^{-a}.\qquad(7.4)$$
--   Its number of operations is at most $N^C$, where $C$ depends only on the fixed parameters.
--
--   This gives polynomial-time estimates of all low-degree spin correlations and of the free energy of Ising spin glasses with interactions of order at least three, throughout the replica-symmetric phase. The estimates resolve instance-to-instance fluctuations.
--
--   **Formalization Note** The algorithm is one deterministic program of the published log-cost rational RAM for all $N$. It reads $N$, an overflow flag, and $O(\log N)$-bit roundings of $\beta$, the $\lambda_p$ and the couplings on a Gaussian box (`IsingBitIO`). The probability is over the exact Gaussian couplings.
--
--   Differences from the source:
--   - encoding: 0 ≤ β < β*, β* the endpoint of the interval on which the limiting pressure equals log 2 + β²ξ(1)/2 → BelowStaticTransition P lam β: some b > β with (1/N) E_J log Z_N(β', J) → log 2 + β'²ξ(1)/2 for every β' ∈ [0, b]; reason: equivalent to β < β* for an interval starting at 0; avoids an sSup junk value; the limiting pressure is read as the limit of the mean pressure
--   - encoding: the mixture in (7.1): P ⊆ {3, …, P} nonempty, λ_p > 0 → P : Finset ℕ nonempty with every p ≥ 3, lam : ℕ → ℝ with lam p > 0 on P; sites Fin N, spins Bool; reason: the same data
--   - reading: a deterministic classical algorithm … Its number of operations is at most N^C → one deterministic program (no coin instruction) of the published log-cost rational RAM BlottoFPTAS.Main.BitRAM for all N, halting on every input with bitCost ≤ N^C for every N ≥ 2; reason: App. L.10 (p.169) proves 'the bit-complexity statement'; a bit-cost bound also bounds the number of operations, and C may absorb finitely many small N
--   - encoding: the input (β, J) and the finite-precision input of App. L.10 → bitInput: N, an overflow flag for max_e |J_e| > C₀⌈log₂(N+2)⌉, and the prec(N)-bit dyadic roundings of β, of every λ_p and of every coupling, prec(N) ≤ C_b⌈log₂(N+2)⌉, with C₀, C_b, prec chosen with the program; reason: L.10: 'The finite input records rounded coordinates and an overflow flag', O(log N) fractional bits; a fixed program cannot store the unboundedly many bits of β and λ_p it needs as N grows, so they are input as roundings like the couplings
--   - encoding: outputs m̂_A (|A| ≤ ℓ) and L̂; the event in (7.4) → the output decodes as #targets + 1 rationals (sets of size ≤ ℓ in a fixed order, then L̂); a non-decoding output counts as failure; the probability is the outer measure of the failure set under the exact Gaussian couplings, the targets at the exact J and β; reason: bit outputs; failure-on-garbage only strengthens the statement
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Theorem 26, p.59, (7.1)–(7.4); App. L.10, pp.168–169

import Mathlib
import Definitions.Def_SYKCavity_Supplement_IsingBitIO

open MeasureTheory

namespace SYKCavity.Supplement

open BlottoFPTAS.Main

/-- **Theorem 26 (Ising thermal expectations and partition function)**, p.59 of A. Schmidhuber,
A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass transition*,
arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), (7.1)–(7.4); bit model App. L.10,
pp.168–169.

Fix the mixture in (7.1) (a nonempty finite set `P` of orders, all `≥ 3`, and `λ_p > 0`), an inverse
temperature `0 ≤ β < β*`, an observable degree `ℓ ≥ 0`, and exponents `a, c > 0`. There is a
deterministic classical algorithm that outputs `m̂_A(β, J)` for all `|A| ≤ ℓ` and `L̂(β, J)` such
that, for all sufficiently large `N`,
`Pr_J[Σ_{|A|≤ℓ} |m̂_A − ⟨σ_A⟩_{β,J}|² > N^{−2c} or |L̂ − log Z_N(β, J)| > N^{−c}] ≤ N^{−a}`.
Its number of operations is at most `N^C`, where `C` depends only on the fixed parameters.

**Formalization Note.**
* `β < β*` is `BelowStaticTransition P lam β`.
* The algorithm is one deterministic `BitRAM` program for all `N`, run on `bitInput`: `N`, an
  overflow flag for `max_e |J_e| > C₀⌈log₂(N+2)⌉`, and the `prec N`-bit dyadic roundings of `β`,
  the `λ_p` and the couplings, with `prec N ≤ C_b⌈log₂(N+2)⌉`. The program, `C`, `C_b`, `C₀` and
  `prec` are chosen after `(P, λ, β, ℓ, a, c)` and before `N`.
* The bit cost is at most `N^C` and the run halts on every input, for every `N ≥ 2`; the failure
  probability (an output that does not decode counts as failure) is over the exact Gaussian
  couplings, with targets at the exact `J` and `β` (outer measure, no measurability assumed). -/
theorem theorem_26 (P : Finset ℕ) (hPne : P.Nonempty) (hP : ∀ p ∈ P, 3 ≤ p) (lam : ℕ → ℝ)
    (hlam : ∀ p ∈ P, 0 < lam p) (β : ℝ) (hβ0 : 0 ≤ β) (hβ : BelowStaticTransition P lam β)
    (ℓ : ℕ) (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∃ prog : BitRAM.Program, BitRAM.Deterministic prog ∧
      ∃ C Cb : ℕ, ∃ C₀ : ℝ, ∃ prec : ℕ → ℕ, (∀ N, prec N ≤ Cb * logLen N) ∧
        (∀ N : ℕ, 2 ≤ N → ∀ J : CIdx P N → ℝ,
          BitRAM.Halts prog (bitInput P lam prec C₀ N β J) BitRAM.zeroTape ∧
            BitRAM.bitCost prog (bitInput P lam prec C₀ N β J) BitRAM.zeroTape ≤ N ^ C) ∧
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          couplingLaw P N {J | Fails P lam ℓ c prog prec C₀ N β J} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-a)) := by sorry

end SYKCavity.Supplement
