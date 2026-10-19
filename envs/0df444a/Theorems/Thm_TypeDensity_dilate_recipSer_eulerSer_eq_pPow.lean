-- Prove2me | Theorems.Thm_TypeDensity_dilate_recipSer_eulerSer_eq_pPow
-- name    : TypeDensity.dilate_recipSer_eulerSer_eq_pPow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:52:53.919384+00:00
-- url     : https://prove2.me/theorems/18a2bc13-7cdc-466d-8fdb-31febc2d2735
-- title:
--   `S(G_aᵛ) = P_{1/q}(S(B_aᵛ))`.
-- statement:
--   `S(G_aᵛ) = P_{1/q}(S(B_aᵛ))`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L878-L886

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_recipRat_X
import Theorems.Thm_TypeDensity_constantCoeff_clusterSer
import Theorems.Thm_TypeDensity_coeff_recipSer
import Theorems.Thm_TypeDensity_dilate_pPow
import Theorems.Thm_TypeDensity_recipSer_pPow
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.dilate_recipSer_eulerSer_eq_pPow (a : ℕ) :
    dilate (recipSer (eulerSer 0 a)) =
      pPow (RatFunc.X : RatFunc ℚ)⁻¹ (dilate (recipSer (clusterSer a))) := by sorry
