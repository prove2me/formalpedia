-- Prove2me | Theorems.Thm_ProxAltMin_Conv_proposition_3
-- name    : ProxAltMin.Conv.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:54.233868+00:00
-- url     : https://prove2.me/theorems/7c07cc02-dbf7-4127-bea2-30bef25d3afb
-- title:
--   Proposition 3 — ∂L(x, y) = (∂f(x) + ∇ₓQ(x, y)) × (∂g(y) + ∇ᵧQ(x, y)) = ∂ₓL(x, y) × ∂ᵧL(x, y) on dom L
-- statement:
--   Let $L(x,y)=f(x)+Q(x,y)+g(y)$ satisfy assumption (H): $f$, $g$ proper lower semicontinuous with values in $\mathbb R\cup\{+\infty\}$, $Q$ of class $C^1$ with $\nabla Q$ Lipschitz on bounded sets. Write $\partial$ for the limiting subdifferential, $\partial_xL(x,y)$ for the limiting subdifferential of $L(\cdot,y)$ at $x$ and $\partial_yL(x,y)$ for that of $L(x,\cdot)$ at $y$.
--
--   Then $\operatorname{dom}L=\operatorname{dom}f\times\operatorname{dom}g$, and for every $(x,y)\in\operatorname{dom}L$,
--   $$\partial L(x,y)=\{\partial f(x)+\nabla_xQ(x,y)\}\times\{\partial g(y)+\nabla_yQ(x,y)\}=\partial_xL(x,y)\times\partial_yL(x,y).$$
--
--   The subdifferential of the coupled objective splits into the two partial subdifferentials. This is what turns the optimality conditions of the two alternating proximal steps into an element of $\partial L$.
--
--   **Formalization Note** $\operatorname{dom}L$ is the set where $L<+\infty$. The set $\{\partial f(x)+\nabla_xQ(x,y)\}$ is the image of $\partial f(x)$ under $a\mapsto a+\nabla_xQ(x,y)$.
-- source:
--   Attouch, Bolte, Redont, Soubeyran, Proximal alternating minimization and projection methods for nonconvex problems, Math. Oper. Res. (2010), p. 5, Proposition 3

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_ProxAltMin_Conv_Setting
open NonconvexSplitting.Shared
open Filter Topology

namespace ProxAltMin.Conv

/-- Proposition 3 (p. 5): under (H), `dom L = dom f × dom g`, and for every `(x, y) ∈ dom L`,
`∂L(x, y) = {∂f(x) + ∇ₓQ(x, y)} × {∂g(y) + ∇ᵧQ(x, y)} = ∂ₓL(x, y) × ∂ᵧL(x, y)`, where `∂ₓL(x, y)` is
the limiting subdifferential of `L(·, y)` at `x` and `∂ᵧL(x, y)` that of `L(x, ·)` at `y`. -/
theorem proposition_3 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (hH : AssumptionH f Q g) :
    (∀ x : EuclideanSpace ℝ (Fin n), ∀ y : EuclideanSpace ℝ (Fin m),
      L f Q g (pt x y) ≠ ⊤ ↔ (f x ≠ ⊤ ∧ g y ≠ ⊤)) ∧
    ∀ x : EuclideanSpace ℝ (Fin n), ∀ y : EuclideanSpace ℝ (Fin m), f x ≠ ⊤ → g y ≠ ⊤ →
      LimitingSubdiff (L f Q g) (pt x y) =
          {v : Z n m | v.fst ∈ (fun a => a + gradX Q (pt x y)) '' LimitingSubdiff f x ∧
            v.snd ∈ (fun b => b + gradY Q (pt x y)) '' LimitingSubdiff g y} ∧
      LimitingSubdiff (L f Q g) (pt x y) =
          {v : Z n m | v.fst ∈ LimitingSubdiff (fun u => L f Q g (pt u y)) x ∧
            v.snd ∈ LimitingSubdiff (fun w => L f Q g (pt x w)) y} := by sorry

end ProxAltMin.Conv
