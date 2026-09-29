-- Prove2me | Theorems.Thm_PNTA_ResidueTheoremAtOrigin_prime
-- name    : PNTA.ResidueTheoremAtOrigin_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T05:50:05.346807+00:00
-- url     : https://prove2.me/theorems/685adbdc-cb5b-4402-a1c1-e9b2c5e44b5c
-- title:
--   Residue theorem at the origin: $\oint c/s \, ds = 2\pi i\,c$
-- statement:
--   The residue theorem for the simplest possible integrand, on a rectangle straddling the origin.
--
--   Let $z$ and $w$ be corners with $\mathrm{Re}\, z < 0 < \mathrm{Re}\, w$ and $\mathrm{Im}\, z < 0 < \mathrm{Im}\, w$, so that the rectangle with these opposite corners contains the origin in its interior. Then for every constant $c \in \mathbb{C}$,
--   $$\oint_{z}^{w} \frac{c}{s}\, ds \;=\; 2\pi i\, c .$$
--
--   This is the base case of the whole residue calculus on rectangles: the value depends only on the residue $c$ at the enclosed pole and not on the size or shape of the rectangle. It is proved by evaluating the four side integrals of $1/s$ explicitly — the real parts cancel in pairs and the imaginary parts assemble into the total turning $2\pi$ of the argument around the origin.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L561-L582

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

theorem PNTA.ResidueTheoremAtOrigin_prime {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by sorry
