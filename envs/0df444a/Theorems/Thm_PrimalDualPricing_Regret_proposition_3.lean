-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_proposition_3
-- name    : PrimalDualPricing.Regret.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:25:55.714867+00:00
-- url     : https://prove2.me/theorems/045d8906-9c45-449a-a1ba-1dd2bf4bb86b
-- title:
--   Proposition 3, p. 16 — when $z^*>0$, $R^\pi_n(T,c)=O((\log n)^{2+18\epsilon}n^{-1/2})$
-- statement:
--   Under Assumptions 1–2 and Remark 2, with $M\ge1$ consumer types, suppose $z^*>0$ (insufficient capacity). For every sufficiently small $\epsilon>0$ there is a constant $C$, independent of $n$, such that the regret of Algorithm 1 with parameter $\epsilon$ satisfies, for every $n\ge3$,
--   $$R^\pi_n(T,c)\le C(\log n)^{2+18\epsilon}n^{-1/2}.$$
--
--   This is the insufficient-capacity case of Theorem 1.
--
--   **Formalization Note** As in Proposition 2, the formalized part is the regret conclusion for the real system (inventory $\lfloor nc\rfloor$). The intermediate bound for the modified system is not stated.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 16, §4.2, Proposition 3

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_System

namespace PrimalDualPricing.Regret

open MeasureTheory ProbabilityTheory

/-- Proposition 3 (Chen–Gallego, arXiv:1812.09234v3, p. 16), the regret part: when `z* > 0` (insufficient
capacity), `R^π_n(T, c) = O((log n)^{2+18ε} n^{−1/2})`. Under Assumptions 1–2 and Remark 2 with `M ≥ 1`
types and `z* > 0`, for every sufficiently small `ε > 0` there is `C`, independent of `n`, such that for every
`n ≥ 3` the regret of Algorithm 1 with parameter `ε` is at most `C (log n)^{2+18ε} n^{−1/2}`. -/
theorem proposition_3 {M : ℕ} (hM : 0 < M) (S : Setting M) (hz : 0 < S.zstar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₀ → ∃ C : ℝ,
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (N : Fin M → ℝ → Ω → ℕ), IndepPoissonPaths N →
        ∀ n : ℕ, 3 ≤ n →
          S.regret eps n N ≤ C * Real.log n ^ (2 + 18 * eps) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by sorry

end PrimalDualPricing.Regret
