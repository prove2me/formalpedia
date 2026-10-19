-- Prove2me | Theorems.Thm_TypeDensity_monic_coeff_sub_mem_iff
-- name    : TypeDensity.monic_coeff_sub_mem_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:07.926228+00:00
-- url     : https://prove2.me/theorems/d5dbdbea-1d7c-428b-bb9a-b32c909f27bb
-- title:
--   For monic polynomials of the same degree `N`, coefficientwise congruence modulo `I` below degree `N` is equivalent to congruence of all coefficients.
-- statement:
--   For monic polynomials of the same degree `N`, coefficientwise congruence modulo `I` below degree `N` is equivalent to congruence of all coefficients.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L704-L712

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.monic_coeff_sub_mem_iff {O : Type} [CommRing O] (I : Ideal O) (N : ℕ)
    (P Q : Polynomial O) (hP : P.Monic) (hQ : Q.Monic) (hPd : P.natDegree = N)
    (hQd : Q.natDegree = N) :
    (∀ j : Fin N, P.coeff j - Q.coeff j ∈ I) ↔ ∀ j, P.coeff j - Q.coeff j ∈ I := by sorry
