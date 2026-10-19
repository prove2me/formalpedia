-- Prove2me | Theorems.Thm_TypeDensity_monic_polynomial_degree
-- name    : TypeDensity.monic_polynomial_degree
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:01.370985+00:00
-- url     : https://prove2.me/theorems/8b6d4304-1c18-484d-8484-9536263b6091
-- title:
--   The polynomial `Xⁿ + ∑ aᵢ Xⁱ` is monic of degree `n`.
-- statement:
--   The polynomial `Xⁿ + ∑ aᵢ Xⁱ` is monic of degree `n`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L902-L912

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.monic_polynomial_degree (O : Type) [CommRing O] [IsDomain O] (n : ℕ) (a : Fin n → O) :
    (monicPolynomial O a).Monic ∧ (monicPolynomial O a).natDegree = n := by sorry
