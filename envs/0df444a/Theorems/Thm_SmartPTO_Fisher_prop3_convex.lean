-- Prove2me | Theorems.Thm_SmartPTO_Fisher_prop3_convex
-- name    : SmartPTO.Fisher.prop3_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:04:14.606981+00:00
-- url     : https://prove2.me/theorems/faf9a3c8-4c81-4da0-8349-33cb90c278bd
-- title:
--   Proposition 3.2 — convexity of the SPO+ loss in the prediction
-- statement:
--   Let $S\subseteq\mathbb R^d$ be nonempty, compact, and convex, with an arbitrary optimal-decision oracle $w^*$. For each fixed realized cost vector $c$,
--
--   $$\hat c\longmapsto\ell_{\mathrm{SPO+}}(\hat c,c)\quad\text{is convex on }\mathbb R^d.$$
--
--   This is the surrogate's structural property used in the paper's population-risk analysis.
--
--   **Formalization Note** Convexity is stated on the entire Euclidean prediction space, with no restriction on the oracle's tie-breaking.
-- source:
--   Elmachtoub & Grigas, Smart "Predict, then Optimize", arXiv:1710.08005v5, p. 18, Proposition 3.2; §2 standing assumptions pp. 8–9

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SmartPTO_Fisher_Setting

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace SmartPTO.Fisher

/-- Proposition 3.2, p. 18: SPO+ is convex in the prediction for fixed realized cost. -/
theorem prop3_convex {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (c : EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (fun chat => spoPlusLoss S wstar chat c) := by sorry

end SmartPTO.Fisher
