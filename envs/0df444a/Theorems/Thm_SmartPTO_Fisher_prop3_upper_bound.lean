-- Prove2me | Theorems.Thm_SmartPTO_Fisher_prop3_upper_bound
-- name    : SmartPTO.Fisher.prop3_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:05.988062+00:00
-- url     : https://prove2.me/theorems/7924fc03-0b35-421d-a9b8-f0b9812081f1
-- title:
--   Proposition 3.1 — the SPO+ loss upper-bounds the SPO loss
-- statement:
--   Let $S\subseteq\mathbb R^d$ be nonempty, compact, and convex, and let $w^*$ return an optimizer of $\min_{w\in S}c^\top w$ for each cost vector $c$. For every realized cost $c$ and prediction $\hat c$,
--
--   $$\ell_{\mathrm{SPO}}(\hat c,c)\le\ell_{\mathrm{SPO+}}(\hat c,c).$$
--
--   Thus the convex surrogate bounds the unambiguous decision loss pointwise.
--
--   **Formalization Note** Both extrema are real infima or suprema, made genuine by the nonempty compact feasible region. The oracle is arbitrary among optimal decisions.
-- source:
--   Elmachtoub & Grigas, Smart "Predict, then Optimize", arXiv:1710.08005v5, p. 18, Proposition 3.1; §2 standing assumptions pp. 8–9

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SmartPTO_Fisher_Setting

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace SmartPTO.Fisher

/-- Proposition 3.1, p. 18: the SPO+ loss upper-bounds the unambiguous SPO loss. -/
theorem prop3_upper_bound {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (c chat : EuclideanSpace ℝ (Fin d)) :
    spoLoss S chat c ≤ spoPlusLoss S wstar chat c := by sorry

end SmartPTO.Fisher
