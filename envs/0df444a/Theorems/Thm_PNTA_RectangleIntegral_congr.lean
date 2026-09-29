-- Prove2me | Theorems.Thm_PNTA_RectangleIntegral_congr
-- name    : PNTA.RectangleIntegral_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T05:49:05.839575+00:00
-- url     : https://prove2.me/theorems/8ad6bb69-1b2a-4ffe-b5ba-ed9ff89d1e35
-- title:
--   The rectangle integral depends only on the values on the boundary
-- statement:
--   The contour integral around an axis-parallel rectangle depends only on the integrand's restriction to the boundary.
--
--   For $z, w \in \mathbb{C}$ let $\partial\mathrm{Rect}(z,w)$ denote the boundary of the rectangle with opposite corners $z$ and $w$, and let $\oint_{z}^{w} f$ denote the integral of $f$ around it (the two horizontal segments minus the two vertical ones, in the standard orientation). If $f$ and $g$ agree at every point of $\partial\mathrm{Rect}(z,w)$, then
--   $$\oint_{z}^{w} f \;=\; \oint_{z}^{w} g .$$
--
--   A congruence lemma of this kind is used constantly when an integrand is modified away from the contour — for instance replacing a function by an analytic continuation that agrees on the boundary but not inside.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L177-L186

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

theorem PNTA.RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by sorry
