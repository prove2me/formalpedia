-- Prove2me | Theorems.Thm_TypeDensity_reduced_form_eq_of_residue_coeff
-- name    : TypeDensity.reduced_form_eq_of_residue_coeff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:37.956882+00:00
-- url     : https://prove2.me/theorems/559398f3-cf24-4fa5-bbe3-52fa1125da53
-- title:
--   If the residues of `c₀, …, c_d` are the coefficients of `H` with `deg H ≤ d`, then `∑ c̄ᵢ Xⁱ = H`.
-- statement:
--   If the residues of `c₀, …, c_d` are the coefficients of `H` with `deg H ≤ d`, then `∑ c̄ᵢ Xⁱ = H`.
-- source:
--   TypeDensity/Blowup/NilpotentGluing.lean#L505-L515

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.reduced_form_eq_of_residue_coeff (R : Type) [CommRing R] [IsLocalRing R] (d : ℕ)
    (c : Fin (d + 1) → R) (H : Polynomial (IsLocalRing.ResidueField R)) (hH : H.natDegree ≤ d)
    (hcH : ∀ i : Fin (d+1), IsLocalRing.residue R (c i) = H.coeff i.val) :
    (∑ i : Fin (d+1), Polynomial.C (IsLocalRing.residue R (c i)) * Polynomial.X^i.val : Polynomial
      (IsLocalRing.ResidueField R)) = H := by sorry
