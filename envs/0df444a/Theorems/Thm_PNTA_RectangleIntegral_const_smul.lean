-- Prove2me | Theorems.Thm_PNTA_RectangleIntegral_const_smul
-- name    : PNTA.RectangleIntegral.const_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T05:47:08.019345+00:00
-- url     : https://prove2.me/theorems/d92b72bb-4bee-4676-9d96-93f8427480e0
-- title:
--   Constants pull out of the rectangle integral
-- statement:
--   Scalar multiples pass through the rectangle contour integral.
--
--   For any $f : \mathbb{C} \to E$ with values in a complex normed space, any corners $z, w$, and any constant $c \in \mathbb{C}$,
--   $$\oint_{z}^{w} c\,f(s)\,ds \;=\; c \oint_{z}^{w} f(s)\,ds .$$
--
--   Note there is no integrability hypothesis: the identity holds unconditionally, because in the convention used here a non-integrable piece contributes zero on both sides. Pulling constants out is the most frequently used manipulation in residue computations.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L467-L470

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
import Definitions.Def_ResidueCalcOnRectangles_defs

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem PNTA.RectangleIntegral.const_smul (f : ℂ → E) (z w c : ℂ) :
    RectangleIntegral (fun s => c • f s) z w = c • RectangleIntegral f z w := by sorry
