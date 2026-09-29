-- Prove2me | Theorems.Thm_PNTA_HasSimplePolesOn_mono
-- name    : PNTA.HasSimplePolesOn.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T05:43:36.609254+00:00
-- url     : https://prove2.me/theorems/769b4cda-0f88-42c7-a9f9-ba157146d5a4
-- title:
--   Having simple poles is inherited by subsets
-- statement:
--   The simple-pole property restricts to smaller sets.
--
--   If $f$ has at worst simple poles at every point of a set $t \subseteq \mathbb{C}$, and $s \subseteq t$, then $f$ has at worst simple poles at every point of $s$.
--
--   This monotonicity is used to shrink the region under consideration — for instance from a large rectangle to a small square around a single pole — while keeping the pole hypothesis available for the residue computation.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L744-L748

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
import Definitions.Def_PNTA_ResidueRect

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem PNTA.HasSimplePolesOn.mono {f : ℂ → ℂ} {s t : Set ℂ}
    (h : HasSimplePolesOn f t) (hst : s ⊆ t) : HasSimplePolesOn f s := by sorry
