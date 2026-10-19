-- Prove2me | Theorems.Thm_TypeDensity_algebraMap_injective_of_tower
-- name    : TypeDensity.algebraMap_injective_of_tower
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:03.783269+00:00
-- url     : https://prove2.me/theorems/996cb071-f3b5-4ff9-b823-bf4242d08a3e
-- title:
--   `O` embeds into any `O`-subring `S` of a field `L` over `K = Frac O`.
-- statement:
--   `O` embeds into any `O`-subring `S` of a field `L` over `K = Frac O`.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L125-L133

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

theorem TypeDensity.algebraMap_injective_of_tower (O : Type) [CommRing O] [IsDomain O] (S L : Type)
    [CommRing S] [Field L] [Algebra O S] [Algebra S L] [Algebra (BaseField O) L] [Algebra O L]
    [IsScalarTower O S L] [IsScalarTower O (BaseField O) L] :
    Function.Injective (algebraMap O S) := by sorry
