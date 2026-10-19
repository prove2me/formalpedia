-- Prove2me | Theorems.Thm_TypeDensity_monic_poly_reconstruct
-- name    : TypeDensity.monic_poly_reconstruct
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:01.292976+00:00
-- url     : https://prove2.me/theorems/a08f0661-58c6-4a29-ac92-598e5060bd6d
-- title:
--   `monicPolyO a = Xⁿ + Σ aᵢ Xⁱ` is monic of degree `n` with lower coefficients `a`, and every monic polynomial of degree `n` arises from its coefficient vector.
-- statement:
--   `monicPolyO a = Xⁿ + Σ aᵢ Xⁱ` is monic of degree `n` with lower coefficients `a`, and every monic polynomial of degree `n` arises from its coefficient vector.
-- source:
--   TypeDensity/Unramified/FactorCells.lean#L100-L124

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

theorem TypeDensity.monic_poly_reconstruct (O : Type) [CommRing O] [Nontrivial O] (n : ℕ) (a : Fin n → O) :
    (monicPolyO a).Monic ∧ (monicPolyO a).natDegree = n
      ∧ (∀ i : Fin n, (monicPolyO a).coeff i = a i)
      ∧ (∀ F : Polynomial O, F.Monic → F.natDegree = n → monicPolyO (coeffVec n F) = F) := by sorry
