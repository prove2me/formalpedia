-- Prove2me | Theorems.Thm_TypeDensity_closure_finite_ascent_root
-- name    : TypeDensity.closure_finite_ascent_root
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:46.805294+00:00
-- url     : https://prove2.me/theorems/0959d47c-a1f9-4512-9730-0d04fae82a38
-- title:
--   The ascent step: let `O → Oδ` be finite, `K = Frac O`, and `Kδ/K` finite separable (with compatible structures).
-- statement:
--   The ascent step: let `O → Oδ` be finite, `K = Frac O`, and `Kδ/K` finite separable (with compatible structures). If `g` is monic irreducible over `K` with finite `O`-closure of `K[X]/(g)`, and `h` is an irreducible factor of `g` over `Kδ`, then the `Oδ`-closure of `Kδ[X]/(h)` is finite over `Oδ`.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L293-L320

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Theorems.Thm_TypeDensity_closure_finite_ascent
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

theorem TypeDensity.closure_finite_ascent_root (O Oδ K Kδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [Algebra O Oδ] [Module.Finite O Oδ]
    [Field K] [Algebra O K] [IsFractionRing O K] [Field Kδ] [Algebra K Kδ] [Algebra O Kδ]
    [Algebra Oδ Kδ] [IsScalarTower O K Kδ] [IsScalarTower O Oδ Kδ] [FiniteDimensional K Kδ]
    [Algebra.IsSeparable K Kδ] (g : K[X]) (hgm : g.Monic) (hgi : Irreducible g)
    (hfin : Module.Finite O (integralClosure O (AdjoinRoot g)))
    (h : Kδ[X]) (hhi : Irreducible h) (hdvd : h ∣ g.map (algebraMap K Kδ)) :
    Module.Finite Oδ (integralClosure Oδ (AdjoinRoot h)) := by sorry
