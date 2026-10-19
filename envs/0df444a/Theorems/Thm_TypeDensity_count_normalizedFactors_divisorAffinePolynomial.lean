-- Prove2me | Theorems.Thm_TypeDensity_count_normalizedFactors_divisorAffinePolynomial
-- name    : TypeDensity.count_normalizedFactors_divisorAffinePolynomial
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:29.438375+00:00
-- url     : https://prove2.me/theorems/3d707d55-23ce-4b3a-b22f-0f25a8baa324
-- title:
--   The multiplicity of an affine direction `φ` in `c · divisorAffinePolynomial Dv` is `Dv φ`;
-- statement:
--   The multiplicity of an affine direction `φ` in `c · divisorAffinePolynomial Dv` is `Dv φ`; in particular `φ` divides it iff `Dv φ > 0`.
-- source:
--   TypeDensity/Blowup/Directions.lean#L112-L152

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
set_option autoImplicit false

open TypeDensity
open scoped Classical

theorem TypeDensity.count_normalizedFactors_divisorAffinePolynomial (k : Type) [Field k]
    (Dv : ExceptionalDivisor k) (lc : k) (hlc : lc ≠ 0) (φ : AffineDirection k) :
    Multiset.count φ.val (UniqueFactorizationMonoid.normalizedFactors
        (Polynomial.C lc * divisorAffinePolynomial k Dv)) = Dv (some φ) ∧
        (φ.val ∣ divisorAffinePolynomial k Dv ↔ 0 < Dv (some φ)) := by sorry
