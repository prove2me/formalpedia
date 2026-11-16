-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_theorem_4_4
-- name    : QuantumStateIdentity321.Schur.Supplement.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:59:30.924795+00:00
-- url     : https://prove2.me/theorems/188b6720-2cfa-4b82-a477-a19e7e87276c
-- title:
--   Theorem 4.4 — completeness of Algorithm 3 with exact Schur transforms: error $\delta/2$ with $2L=O((1-2\sqrt\varepsilon)^{-2}\log(n/\delta))$ copies
-- statement:
--   Let $n\ge2$ and $d\ge2$, let $\varepsilon\in(0,1/4)$ and $\delta\in(0,1)$, and set $\gamma=\frac12-\sqrt\varepsilon$, $\tau=\frac{3n-4}4-\frac{n-2}2\varepsilon+\frac{n-2}4\sqrt\varepsilon$ and $L=\lceil(8/\gamma^2)\log(2n/\delta)\rceil$. Then Algorithm 3 with exact Schur transforms and $L$ rounds, a tester using $2L$ copies of each input state, accepts every yes instance of $\mathrm{QSI}^\varepsilon_n$ with probability at least $1-\delta/2$, and there is an absolute constant $C$ with
--
--   $$
--   2L\le\frac{C}{(1-2\sqrt\varepsilon)^2}\log(n/\delta).
--   $$
--
--   Together with Theorem 4.3 (1), Algorithm 3 with exact transforms solves $\mathrm{QSI}^\varepsilon_n$ with error $\delta/2$ using $O(\gamma^{-2}\log(n/\delta))$ copies of each state.
--
--   **Formalization Note** The algorithm is its accept effect on $2L$ copies of each state, as in Theorem 4.3; the constant $C$ is quantified before $n,d,\varepsilon,\delta$.
--
--   Differences from the source:
--   - encoding: Algorithm 3 with exact Schur transforms as a procedure → a published Tester with effect alg3Effect; reason: every procedure ending in accept/reject has such an effect; same algorithm
--   - encoding: 2L = O((1−2√ε)⁻² log(n/δ)) → 2L ≤ C (1−2√ε)⁻² log(n/δ) with ∃ C > 0 before n, d, ε, δ; reason: the meaning of the O(·)
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Theorem 4.4, PDF/printed p.17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_SchurSampling

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- Theorem 4.4 (completeness), p.17: for `n ≥ 2`, `d ≥ 2`, `ε ∈ (0, 1/4)` and `δ ∈ (0, 1)`,
Algorithm 3 with exact Schur transforms and `L = ⌈(8/γ²) log(2n/δ)⌉` rounds (`γ = 1/2 − √ε`,
threshold `τ` as in Algorithm 3), as a tester using `2L` copies of each input state, accepts every
yes instance with probability at least `1 − δ/2`, and `2L ≤ C (1 − 2√ε)⁻² log(n/δ)` for an
absolute constant `C`. -/
theorem theorem_4_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), 2 ≤ n → 2 ≤ d →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 / 4 → 0 < δ → δ < 1 →
        (∃ T : Tester n (2 * alg3Rounds n ε δ) d,
          T.effect = alg3Effect n d (alg3Rounds n ε δ) (alg3Threshold n ε) ∧
          ∀ ψ : Fin n → State d, (∀ i, ‖ψ i‖ = 1) → IsYesInstance ε ψ →
            1 - δ / 2 ≤ acceptProb T ψ) ∧
        ((2 * alg3Rounds n ε δ : ℕ) : ℝ) ≤
          C * (1 / (1 - 2 * Real.sqrt ε) ^ 2) * Real.log (n / δ) := by sorry

end QuantumStateIdentity321.Schur.Supplement
