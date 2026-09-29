-- Prove2me | Theorems.Thm_PNTA_ContinuousOn_rectangleBorder_integrable
-- name    : PNTA.ContinuousOn.rectangleBorder_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T05:42:32.756787+00:00
-- url     : https://prove2.me/theorems/478fa676-c6f3-43ae-89aa-07d585c25f6e
-- title:
--   A function continuous on the rectangle boundary is boundary-integrable
-- statement:
--   Continuity on the contour suffices for the rectangle integral to make sense.
--
--   If $f$ is continuous at every point of the boundary $\partial\mathrm{Rect}(z,w)$ of the rectangle with opposite corners $z$ and $w$, then $f$ is integrable along each of the four sides — that is, $f$ is boundary-integrable over that rectangle.
--
--   Each side is a compact segment, and a continuous function on a compact interval is integrable there; the content is the bookkeeping that the four parametrised sides land inside the boundary set. This is the standard way integrability hypotheses are discharged in practice, since integrands arising from analytic functions are continuous wherever they have no poles.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L222-L229

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

omit [NormedSpace ℂ E] in

theorem PNTA.ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w := by sorry
