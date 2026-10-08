-- Prove2me | Theorems.Thm_SmartPTO_Fisher_prop3_subgradient
-- name    : SmartPTO.Fisher.prop3_subgradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:16.780548+00:00
-- url     : https://prove2.me/theorems/241d44ea-2526-4eca-a2f2-a1bdb624091b
-- title:
--   Proposition 3.3 — an explicit SPO+ subgradient
-- statement:
--   Let $S\subseteq\mathbb R^d$ be nonempty, compact, and convex, and let $w^*$ select an optimal decision for each cost vector. For a realized cost $c$ and prediction $\hat c$, the vector $2(w^*(c)-w^*(2\hat c-c))$ is a subgradient of the SPO+ loss in its prediction argument. Explicitly, for every $\tilde c\in\mathbb R^d$,
--
--   $$\ell_{\mathrm{SPO+}}(\tilde c,c)\ge\ell_{\mathrm{SPO+}}(\hat c,c)+\left\langle2\bigl(w^*(c)-w^*(2\hat c-c)\bigr),\tilde c-\hat c\right\rangle.$$
--
--   This supplies a concrete subgradient even when the support function is not differentiable.
--
--   **Formalization Note** The inequality uses the paper's definition of subgradient on p. 10. It retains the factor $2$ and the reflected argument $2\hat c-c$.
-- source:
--   Elmachtoub & Grigas, Smart "Predict, then Optimize", arXiv:1710.08005v5, p. 18, Proposition 3.3; subgradient definition p. 10

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SmartPTO_Fisher_Setting

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace SmartPTO.Fisher

/-- Proposition 3.3, p. 18, with the paper's subgradient inequality from p. 10. -/
theorem prop3_subgradient {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (c chat ct : EuclideanSpace ℝ (Fin d)) :
    spoPlusLoss S wstar chat c +
      ⟪(2 : ℝ) • (wstar c - wstar ((2 : ℝ) • chat - c)), ct - chat⟫_ℝ ≤
      spoPlusLoss S wstar ct c := by sorry

end SmartPTO.Fisher
