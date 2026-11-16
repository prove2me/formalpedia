-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_theorem_4_3
-- name    : QuantumStateIdentity321.Schur.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:58:25.195203+00:00
-- url     : https://prove2.me/theorems/410a7c56-4990-4e78-908f-9404cb0ecfe3
-- title:
--   Theorem 4.3 — soundness of Algorithm 3 with exact Schur transforms: error $\delta/2$, also with $\lceil8\gamma^{-2}\log(2/\delta)\rceil$ rounds
-- statement:
--   Let $n\ge2$ and $d\ge2$, let $\varepsilon\in(0,1/4)$ and $\delta\in(0,1)$, and set $\gamma=\frac12-\sqrt\varepsilon$ and $\tau=\frac{3n-4}4-\frac{n-2}2\varepsilon+\frac{n-2}4\sqrt\varepsilon$. Then:
--
--   1. Algorithm 3 with exact Schur transforms and $L=\lceil(8/\gamma^2)\log(2n/\delta)\rceil$ rounds, a tester using $2L$ copies of each input state, rejects every no instance of $\mathrm{QSI}^\varepsilon_n$ with probability at least $1-\delta/2$;
--   2. for soundness alone, $R=\lceil(8/\gamma^2)\log(2/\delta)\rceil$ rounds already suffice: the same algorithm with $R$ rounds, using $2R$ copies of each input state, rejects every no instance with probability at least $1-\delta/2$;
--   3. this is $O\bigl((1-2\sqrt\varepsilon)^{-2}\log(2/\delta)\bigr)$ copies: there is an absolute constant $C$ with
--
--   $$
--   2R\le\frac{C}{(1-2\sqrt\varepsilon)^2}\log(2/\delta).
--   $$
--
--   With Theorem 4.4, and replacing the exact transforms by approximate circuits at a further cost $\delta/2$, this gives the paper's main Theorem 1.3 (p.18).
--
--   **Formalization Note** The algorithm is its accept effect on $2R$ copies of each state (published tester model), and "rejects with probability at least $1-\delta/2$" is stated as "accepts with probability at most $\delta/2$". The constant $C$ is quantified before $n,d,\varepsilon,\delta$.
--
--   Differences from the source:
--   - encoding: Algorithm 3 with exact Schur transforms as a procedure → a published Tester with effect alg3Effect (sum over accepted outcome records of tensor products of the projectors M_{λ,S}); reason: every procedure ending in accept/reject has such an effect; same algorithm
--   - encoding: O((1−2√ε)⁻² log(2/δ)) copies → 2R ≤ C (1−2√ε)⁻² log(2/δ) with ∃ C > 0 before n, d, ε, δ; reason: the meaning of the O(·); the explicit 2R copies are stated as well
--   - encoding: rejects with probability ≥ 1 − δ/2 → accepts with probability ≤ δ/2; reason: the two outcome probabilities sum to 1 on unit inputs
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Theorem 4.3, PDF/printed p.17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_SchurSampling

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- Theorem 4.3 (soundness), p.17: for `n ≥ 2`, `d ≥ 2`, `ε ∈ (0, 1/4)` and `δ ∈ (0, 1)`, with
`γ = 1/2 − √ε` and `τ = (3n−4)/4 − ((n−2)/2)ε + ((n−2)/4)√ε`, Algorithm 3 with exact Schur
transforms

1. with its `L = ⌈(8/γ²) log(2n/δ)⌉` rounds, as a tester using `2L` copies of each input state,
   rejects every no instance with probability at least `1 − δ/2`;
2. with `R = ⌈(8/γ²) log(2/δ)⌉` rounds (`2R` copies of each input state) already rejects every no
   instance with probability at least `1 − δ/2`;
3. `2R ≤ C (1 − 2√ε)⁻² log(2/δ)` for an absolute constant `C`. -/
theorem theorem_4_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), 2 ≤ n → 2 ≤ d →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 / 4 → 0 < δ → δ < 1 →
        (∃ T : Tester n (2 * alg3Rounds n ε δ) d,
          T.effect = alg3Effect n d (alg3Rounds n ε δ) (alg3Threshold n ε) ∧
          ∀ ψ : Fin n → State d, (∀ i, ‖ψ i‖ = 1) → IsNoInstance ε ψ →
            acceptProb T ψ ≤ δ / 2) ∧
        (∃ T : Tester n (2 * alg3RoundsSound ε δ) d,
          T.effect = alg3Effect n d (alg3RoundsSound ε δ) (alg3Threshold n ε) ∧
          ∀ ψ : Fin n → State d, (∀ i, ‖ψ i‖ = 1) → IsNoInstance ε ψ →
            acceptProb T ψ ≤ δ / 2) ∧
        ((2 * alg3RoundsSound ε δ : ℕ) : ℝ) ≤
          C * (1 / (1 - 2 * Real.sqrt ε) ^ 2) * Real.log (2 / δ) := by sorry

end QuantumStateIdentity321.Schur.Supplement
