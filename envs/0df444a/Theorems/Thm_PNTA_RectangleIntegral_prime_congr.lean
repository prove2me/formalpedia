-- Prove2me | Theorems.Thm_PNTA_RectangleIntegral_prime_congr
-- name    : PNTA.RectangleIntegral_prime_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T06:12:32.703484+00:00
-- url     : https://prove2.me/theorems/19c05ef5-4376-44a2-b0dd-8ce84e9400af
-- title:
--   The normalised rectangle integral depends only on the boundary values
-- statement:
--   The same congruence, for the normalised rectangle integral.
--
--   The normalised integral is the contour integral divided by $2\pi i$,
--   $$\frac{1}{2\pi i}\oint_{z}^{w} f ,$$
--   the normalisation that makes the residue theorem read "integral $=$ sum of residues" with no leftover constant. If $f$ and $g$ agree at every point of the rectangle boundary $\partial\mathrm{Rect}(z,w)$, then their normalised rectangle integrals over $z, w$ are equal.
--
--   This is the form actually used in Perron-type contour arguments, where the integrand is normalised once and for all.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L187-L190

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

theorem PNTA.RectangleIntegral_prime_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by sorry
