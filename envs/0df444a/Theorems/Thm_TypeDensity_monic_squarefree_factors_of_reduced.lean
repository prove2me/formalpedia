-- Prove2me | Theorems.Thm_TypeDensity_monic_squarefree_factors_of_reduced
-- name    : TypeDensity.monic_squarefree_factors_of_reduced
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:28.680682+00:00
-- url     : https://prove2.me/theorems/3c70f0aa-00d3-4f10-aec9-d848e9bf1f03
-- title:
--   A monic `F` over a field with `K[X]/(F)` reduced is a product of distinct monic irreducibles.
-- statement:
--   A monic `F` over a field with `K[X]/(F)` reduced is a product of distinct monic irreducibles.
-- source:
--   TypeDensity/Unramified/FactorCells.lean#L177-L205

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.monic_squarefree_factors_of_reduced (K : Type) [Field K] (F : Polynomial K)
    (hF : F.Monic) (hred : IsReduced (AdjoinRoot F)) :
    ∃ gs : List (Polynomial K), (∀ g ∈ gs, g.Monic ∧ Irreducible g) ∧
      gs.Pairwise (fun g h ↦ g ≠ h) ∧ F = gs.prod := by sorry
