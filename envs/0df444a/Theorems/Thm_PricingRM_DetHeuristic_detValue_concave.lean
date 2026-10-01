-- Prove2me | Theorems.Thm_PricingRM_DetHeuristic_detValue_concave
-- name    : PricingRM.DetHeuristic.detValue_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:34:49.510735+00:00
-- url     : https://prove2.me/theorems/e85edfd2-5466-478f-9b49-ca1dcfb98a96
-- title:
--   Appendix, Proof of Proposition 8 — $V_1^{\det}$ is concave in the capacity
-- statement:
--   In the $N$-period model, suppose that for every period $n$ the revenue rate $p \mapsto p\,E[D_n(p)]$ is concave on $[0,\infty)$ and the mean demand $p \mapsto E[D_n(p)]$ is convex on $[0,\infty)$. Let $p^{(1)}$ and $p^{(2)}$ be optimal solutions of the deterministic problem (32)–(33) at capacities $C_1$ and $C_2$, so that $V_1^{\det}(C_i) = \sum_n p^{(i)}_n E[D_n(p^{(i)}_n)]$. Then for every $\theta \in [0,1]$,
--   $$
--   \theta\, V_1^{\det}(C_1) + (1-\theta)\, V_1^{\det}(C_2) \le V_1^{\det}\big(\theta C_1 + (1-\theta) C_2\big).
--   $$
--
--   Concavity of the deterministic value in the capacity is the first step of the paper's proof of Proposition 8; it is what allows Jensen's inequality to be applied to the value of the remaining periods.
--
--   **Formalization Note** $V_1^{\det}(C)$ may be $-\infty$ (infeasible) or $+\infty$ (unbounded) for some capacities, so concavity is stated at capacities $C_1, C_2$ where the problem has an optimal solution; the right-hand side is the `EReal` supremum `detValue`. "Concave objective and convex feasible region" is read as the two per-period hypotheses above, which make (33) convex for every capacity.
-- source:
--   Bitran and Caldentey, An Overview of Pricing Models for Revenue Management, MSOM 5(3) 2003, p. 226, Appendix, Proof of Proposition 8, first sentence

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PricingRM.DetHeuristic

/-- Bitran–Caldentey (2003), Appendix, Proof of Proposition 8, first sentence, p. 226:
`V_1^det` is concave in the capacity. If `p₁` and `p₂` are optimal for (32)–(33) at capacities
`C₁` and `C₂` (so `V_1^det(Cᵢ)` is the objective of `pᵢ`), then for every `θ ∈ [0, 1]`,
`θ V_1^det(C₁) + (1 - θ) V_1^det(C₂) ≤ V_1^det(θ C₁ + (1 - θ) C₂)`. -/
theorem detValue_concave {N : ℕ} (M : PricingModel N)
    (hconc : ∀ n, ConcaveOn ℝ (Set.Ici 0) (fun p => p * meanDemand M n p))
    (hconv : ∀ n, ConvexOn ℝ (Set.Ici 0) (meanDemand M n))
    (C₁ C₂ : ℝ) (p₁ p₂ : Fin N → ℝ) (h₁ : IsDetOptimal M C₁ p₁) (h₂ : IsDetOptimal M C₂ p₂)
    (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    ((θ * detObjective M p₁ + (1 - θ) * detObjective M p₂ : ℝ) : EReal) ≤
      detValue M (θ * C₁ + (1 - θ) * C₂) := by sorry

end PricingRM.DetHeuristic
