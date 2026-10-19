-- Prove2me | Theorems.Thm_TypeDensity_adjoinRoot_tensor
-- name    : TypeDensity.adjoinRoot_tensor
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:04.562975+00:00
-- url     : https://prove2.me/theorems/202d2098-f384-446e-9712-d35d28721e31
-- title:
--   Base change of `R[X]/(g)` along `R → A`: `A ⊗_R R[X]/(g) ≃ A[X]/(g)`, compatibly with `mk`.
-- statement:
--   Base change of `R[X]/(g)` along `R → A`: `A ⊗_R R[X]/(g) ≃ A[X]/(g)`, compatibly with `mk`.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L204-L219

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

theorem TypeDensity.adjoinRoot_tensor (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (g : R[X]) :
    ∃ e : A ⊗[R] AdjoinRoot g ≃ₐ[A] AdjoinRoot (g.map (algebraMap R A)), ∀ P : R[X],
      e (1 ⊗ₜ AdjoinRoot.mk g P) = AdjoinRoot.mk _ (P.map (algebraMap R A)) := by sorry
