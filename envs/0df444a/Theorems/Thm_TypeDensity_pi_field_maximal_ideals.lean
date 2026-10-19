-- Prove2me | Theorems.Thm_TypeDensity_pi_field_maximal_ideals
-- name    : TypeDensity.pi_field_maximal_ideals
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:42.640076+00:00
-- url     : https://prove2.me/theorems/7e2f4973-8b16-4d87-bdfc-a4e02ed64b40
-- title:
--   The maximal ideals of a finite product of fields `∏ Lᵢ` are exactly the kernels of the projections, and distinct projections have distinct kernels.
-- statement:
--   The maximal ideals of a finite product of fields `∏ Lᵢ` are exactly the kernels of the projections, and distinct projections have distinct kernels.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L500-L537

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

theorem TypeDensity.pi_field_maximal_ideals (ι : Type) [Finite ι] (L : ι → Type) [∀ i, Field (L i)]
    (m : Ideal (∀ i, L i)) :
    (m.IsMaximal ↔ ∃ i, m = RingHom.ker (Pi.evalRingHom L i)) ∧ ∀ i j : ι,
      RingHom.ker (Pi.evalRingHom L i) = RingHom.ker (Pi.evalRingHom L j) → i = j := by sorry
