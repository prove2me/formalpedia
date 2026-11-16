-- Prove2me | Theorems.Thm_SeededShannon_Supplement_theorem_7_15
-- name    : SeededShannon.Supplement.theorem_7_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:46:58.2978+00:00
-- url     : https://prove2.me/theorems/0e77c061-8edd-45d3-8fbb-1fe650c4c5f0
-- title:
--   Theorem 7.15 — uniquely decodable seeded codes at Shannon rate
-- statement:
--   Assume the ingredients of Construction 6.1 satisfy their stated definitions, and assume a subexponentially secure two-input correlation-intractable hash family for linearly shifted sparse output relations (Definition 7.6). Then for all constants $0<p<1/4$ and $0<\varepsilon<1-H(p)$, there is a uniquely decodable seeded code with a polynomial minimum message length $k_{\min}(\lambda)$ that, for every polynomially bounded message length $k\ge k_{\min}(\lambda)$, selectively $p$-corrects with unique decoding, has algorithms running in time $\mathrm{poly}(\lambda,k)$, and has rate at least
--   $$1-H(p)-\varepsilon.$$
--
--   Here $H$ is the binary entropy function in bits. By Theorem 7.7 such hash families exist under the subexponential security of DDH, LWE, QR, DCR, or iO with lossy functions.
--
--   **Formalization Note** The ingredients are $i\mathcal O$, a single point binding hash, a puncturable PRF, puncturable $\tau$-robust PRCs for every $\tau<1/2$, and the two evasive obfuscators for all their parameters; the balanced code is supplied unconditionally.
--
--   Differences from the source:
--   - reading: the ingredients of Construction 6.1 satisfy their stated definitions → Ingredients61: iO, SPH, a 1-puncturable PRF, a 1-puncturable τ-robust PRC for every 0 < τ < 1/2, sparse-set obfuscators for every density in (0, 1), partition obfuscators for all (p, τ, γ) and large b; reason: the parameters the construction may need, assumed before p and ε are fixed; the balanced code is unconditional (Theorem 3.14, Lemma 7.5)
--   - reading: a subexponentially secure two-input CI hash for linearly shifted sparse output relations → an efficient CIHash with SubexpCI c s₀ for a polynomial s₀; reason: Theorem 7.7's sparsity threshold s₀ is a polynomial
--   - reading: for every polynomially bounded message length k ≥ k_min(λ) → supported lengths k_min(λ) ≤ k ≤ 2^λ − v(λ) for a polynomial v; reason: the proof's range; every polynomially bounded k is supported for all large λ and correctness is asymptotic
--   - encoding: uniquely decodable; selectively p-corrects with unique decoding → list bound 1 and failure Decode(y) ≠ [x*]; reason: Definition 3.15 identifies a unique output with a list of size at most one
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 7.15, p.53 (PDF p.56); Construction 6.1, pp.37–38; Definition 7.6, p.50

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_SeededShannon_Supplement_SelectivelyCorrectUnique
import Definitions.Def_SeededShannon_Supplement_CIHash
import Definitions.Def_SeededShannon_Supplement_Constr61

set_option autoImplicit false

namespace SeededShannon.Supplement

open NoisyOWMPC SeededShannon

/-- **Theorem 7.15 (Uniquely decodable seeded codes at Shannon rate)** (Dujmovic, Lu, Silbak, Wichs,
*Shannon Rate Seeded Codes from Indistinguishability Obfuscation*, STOC 2027 submission (manuscript
sha256 52f4b606…a769709), Theorem 7.15, p.53): assume the ingredients of Construction 6.1 satisfy
their stated definitions, and assume a subexponentially secure two-input correlation-intractable
hash family for linearly shifted sparse output relations (Definition 7.6). Then for all constants
`0 < p < 1/4` and `0 < ε < 1 − H(p)`, there is a uniquely decodable seeded code with a polynomial
minimum message length `k_min(λ)` that, for every polynomially bounded message length
`k ≥ k_min(λ)`, selectively `p`-corrects with unique decoding, has algorithms running in time
`poly(λ, k)`, and has rate at least `1 − H(p) − ε`.

**Formalization Note** The ingredients are `Ingredients61` (iO, a single point binding hash, a
puncturable PRF, puncturable `τ`-robust PRCs for every `τ < 1/2`, the two evasive obfuscators for
all their parameters; the balanced code is unconditional). The hash family is efficient and
subexponentially secure with some constant `c` and a polynomial sparsity threshold `s₀`
(Theorem 7.7's `s₀`). The supported lengths are `k_min(λ) ≤ k ≤ 2^λ − v(λ)` for a polynomial `v`
(the tag length of the proof); every polynomially bounded `k ≥ k_min` is supported for all large
`λ`, and correctness is asymptotic. Unique decodability is list size `1`; the rate bound
`k/N(λ, k) ≥ 1 − H(p) − ε` holds at every supported length. `H` is the binary entropy in bits. -/
theorem theorem_7_15 (hIng : Ingredients61)
    (hCI : ∃ (H : CIHash) (c : ℝ) (s₀ : ℕ → ℕ), PolyBounded s₀ ∧ H.IsEfficient ∧ H.SubexpCI c s₀) :
    ∀ p ε : ℝ, 0 < p → p < 1 / 4 → 0 < ε → ε < 1 - WildeQIT.binaryEntropy p →
      ∃ (C : SeededCode) (kmin v : ℕ → ℕ), PolyBounded kmin ∧ PolyBounded v ∧
        C.EncodeLength (fun lam k => kmin lam ≤ k ∧ k + v lam ≤ 2 ^ lam) ∧
        C.ListBound (fun lam k => kmin lam ≤ k ∧ k + v lam ≤ 2 ^ lam) (fun _ _ => 1) ∧
        SelectivelyCorrectUnique C (fun lam k => kmin lam ≤ k ∧ k + v lam ≤ 2 ^ lam) p ∧
        C.IsEfficient (fun lam k => kmin lam ≤ k ∧ k + v lam ≤ 2 ^ lam) ∧
        ∀ lam k, kmin lam ≤ k → k + v lam ≤ 2 ^ lam →
          1 - WildeQIT.binaryEntropy p - ε ≤ (k : ℝ) / C.N lam k := by sorry

end SeededShannon.Supplement
