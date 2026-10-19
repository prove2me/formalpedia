-- Prove2me | Theorems.Thm_TypeDensity_root_field_algEquiv_conjugate_orbit
-- name    : TypeDensity.root_field_algEquiv_conjugate_orbit
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:07.648827+00:00
-- url     : https://prove2.me/theorems/442a10a5-b189-4044-883e-5d083ba0630c
-- title:
--   For the unramified extension `Kδ/K` of degree `δ = deg Φ`, a monic irreducible `g` over `Kδ` dividing a monic irreducible `H` over `K` of degree `δ · deg g` has `K[X]/(H) ≃ Kδ[X]/(g)`.
-- statement:
--   For the unramified extension `Kδ/K` of degree `δ = deg Φ`, a monic irreducible `g` over `Kδ` dividing a monic irreducible `H` over `K` of degree `δ · deg g` has `K[X]/(H) ≃ Kδ[X]/(g)`.
-- source:
--   TypeDensity/Unramified/FactorCells.lean#L529-L545

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

theorem TypeDensity.root_field_algEquiv_conjugate_orbit (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O)
    [IsDomain (AdjoinRoot Φ)] (ι : BaseField O →+* BaseField (AdjoinRoot Φ))
    (hfin : letI := ι.toAlgebra; Module.Finite (BaseField O) (BaseField (AdjoinRoot Φ))
    ∧ Module.finrank (BaseField O) (BaseField (AdjoinRoot Φ)) = Φ.natDegree)
    (g : Polynomial (BaseField (AdjoinRoot Φ))) (hg : g.Monic) (hgi : Irreducible g)
    (H : Polynomial (BaseField O)) (hH : H.Monic) (hHi : Irreducible H) (hdiv : g ∣ H.map ι)
    (hdeg : H.natDegree = Φ.natDegree * g.natDegree) :
    letI := ι.toAlgebra; Nonempty (AdjoinRoot H ≃ₐ[BaseField O] AdjoinRoot g) := by sorry
