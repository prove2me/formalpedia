-- Prove2me | Theorems.Thm_TypeDensity_unramified_fraction_base_change
-- name    : TypeDensity.unramified_fraction_base_change
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:27.653826+00:00
-- url     : https://prove2.me/theorems/41d25746-d57a-4e8e-9a79-eec4b405649d
-- title:
--   For a finite free extension of DVRs `O → Oδ` of rank `δ` in which a uniformizer stays irreducible, `K ⊗_O Oδ` is a field of degree `δ` over `K` and a fraction field of `Oδ`.
-- statement:
--   For a finite free extension of DVRs `O → Oδ` of rank `δ` in which a uniformizer stays irreducible, `K ⊗_O Oδ` is a field of degree `δ` over `K` and a fraction field of `Oδ`.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L541-L577

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
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
import Mathlib.RingTheory.Henselian
set_option autoImplicit false

open TypeDensity
open scoped TensorProduct
open Polynomial IsLocalRing

theorem TypeDensity.unramified_fraction_base_change (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [Algebra O Oδ] [Module.Finite O Oδ] [Module.Free O Oδ] (δ : ℕ) (hrank : Module.finrank O Oδ = δ)
    (pi : O) (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi)) :
    IsField (TensorProduct O (BaseField O) Oδ) ∧ Module.finrank (BaseField O)
      (TensorProduct O (BaseField O) Oδ) = δ
      ∧ (letI : Algebra Oδ (TensorProduct O (BaseField O) Oδ) := Algebra.TensorProduct.rightAlgebra;
        IsFractionRing Oδ (TensorProduct O (BaseField O) Oδ)) := by sorry
