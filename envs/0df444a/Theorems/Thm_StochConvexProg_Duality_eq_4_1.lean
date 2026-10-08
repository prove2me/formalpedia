-- Prove2me | Theorems.Thm_StochConvexProg_Duality_eq_4_1
-- name    : StochConvexProg.Duality.eq_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:16:55.061439+00:00
-- url     : https://prove2.me/theorems/1723346a-d8d3-4711-8ab2-42cfd2b42e50
-- title:
--   (4.1), printed as (1.4) — g(y) = inf_u {⟨u, y⟩ + φ(u)} = −φ*(−y)
-- statement:
--   Under the standing assumptions, with $\sigma$ a probability measure, for every $y\in Y$ the dual objective $g(y)=\inf_{x\in X}L(x,y)$ satisfies
--   $$g(y)=\inf_{u\in U}\{\langle u,y\rangle+\varphi(u)\}=-\varphi^*(-y),$$
--   where $\varphi(u)=\inf_{x}F(x,u)$ is the perturbation function and $\varphi^*$ its conjugate on $Y$ with respect to the pairing (1.6).
--
--   This identity expresses the dual problem $\mathbf D$ entirely through the perturbation function $\varphi$, and is the link through which the properties of $\varphi$ become duality statements.
--
--   **Formalization Note** The computation is in `EReal`; $\langle u,y\rangle$ is real, so the sums and differences involved have no ambiguous $\infty-\infty$ cases. No boundedness of $C_1,C_2$ is assumed. The paper prints the display with the label (1.4); it is cited as (4.1) on pp. 192–193.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 188, display (4.1) (printed with the label "(1.4)")

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem
import Definitions.Def_StochConvexProg_Duality_Dual

open MeasureTheory

namespace StochConvexProg.Duality

/-- Rockafellar–Wets (1976), p. 188, (4.1) (printed with the label "(1.4)"):
`g(y) = inf_{u ∈ U} {⟨u, y⟩ + φ(u)} = −φ*(−y)`. -/
theorem eq_4_1 {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂)
    (y : YSpace σ m₁ m₂) :
    pr.dualObj y = (⨅ u : USpace σ m₁ m₂, ((pairUY u y : ℝ) : EReal) + pr.phi u) ∧
      pr.dualObj y = -conjU pr.phi (-y) := by sorry

end StochConvexProg.Duality
