-- Prove2me | Theorems.Thm_TypeDensity_curve_datum_surj_and_inf_clauses
-- name    : TypeDensity.curve_datum_surj_and_inf_clauses
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:38:51.482185+00:00
-- url     : https://prove2.me/theorems/efa4f58e-6b37-4b08-b926-d2716dddb966
-- title:
--   For the strict transform of a degree-`d` form with residue polynomial `H` and homogeneous divisor `Dv` on the concrete surface, the curve datum has a point over every direction in the support of `Dv`,
-- statement:
--   For the strict transform of a degree-`d` form with residue polynomial `H` and homogeneous divisor `Dv` on the concrete surface, the curve datum has a point over every direction in the support of `Dv`, a point at the origin and at infinity when `Dv` charges them, and the multiplicity at infinity is `Dv none`.
-- source:
--   TypeDensity/Blowup/NilpotentGluing.lean#L586-L689

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
import Theorems.Thm_TypeDensity_blowup_chart_relation
import Theorems.Thm_TypeDensity_directionPoint_properties
import Theorems.Thm_TypeDensity_count_normalizedFactors_divisorAffinePolynomial
import Theorems.Thm_TypeDensity_infinity_point_maximal
import Theorems.Thm_TypeDensity_reduced_form_eq_of_residue_coeff
import Theorems.Thm_TypeDensity_overlap_exceptional_point_comap_maximal
import Theorems.Thm_TypeDensity_overlap_exceptional_point_comap_maximal_right
import Theorems.Thm_TypeDensity_concrete_infinity_strict_transform_multiplicity
import Theorems.Thm_TypeDensity_concrete_infinity_point_completion
import Theorems.Thm_TypeDensity_concrete_surface_parameterIdeal_isMaximal
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
import Theorems.Thm_TypeDensity_concrete_surface_data_exists_unconditional
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

theorem TypeDensity.curve_datum_surj_and_inf_clauses (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (d : ℕ) (f : (ConcreteSurface O pi u a b))
    (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (_hc : f = ∑ i : Fin (d + 1), c i * (surfaceT O pi u a b) ^ (d - i.val) *
      (surfaceX O pi u a b) ^ i.val)
    [IsLocalRing (ConcreteSurface O pi u a b)] (H : Polynomial ((IsLocalRing.ResidueField (ConcreteSurface O pi u a b))))
    (Dv : ExceptionalDivisor ((IsLocalRing.ResidueField (ConcreteSurface O pi u a b))))
    (hH : HasHomogeneousDivisor ((IsLocalRing.ResidueField (ConcreteSurface O pi u a b))) d H Dv)
    (hcH : ∀ i : Fin (d+1), IsLocalRing.residue (ConcreteSurface O pi u a b) (c i) = H.coeff i.val)
    (e : (((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ⧸ (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ≃+* Polynomial ((IsLocalRing.ResidueField (ConcreteSurface O pi u a b))))
    (he : ∀ r : ConcreteSurface O pi u a b,
      e (Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) r)) =
        Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) = Polynomial.X)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
      beta)
    (_hleft : ∀ s : D.ι ⊕ D.ι0, leftData D s = completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) (leftPoint D s)
      (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b) ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) (c i) *
        ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))^i.val) ∧ (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
          ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) (c i) * ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))^i.val) ∈ leftPoint D s)
    (hleftsurj : ∀ P : Ideal ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))), P.IsMaximal →
      ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) (surfaceT O pi u a b) ∈ P → (∑ i : Fin (d+1), algebraMap
        (ConcreteSurface O pi u a b) ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) (c i) * ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))^i.val) ∈ P →
      ∃ s : D.ι ⊕ D.ι0, leftPoint D s = P)
    (hright : ∀ s : D.ι ⊕ D.ιinf, Ideal.span {rightData D s} = Ideal.span {completedPointMap
      ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) (rightPoint D s) (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
        ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) (c i) * ((chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)))^(d - i.val))} ∧
      (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b) ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) (c i) *
        ((chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)))^(d - i.val)) ∈ rightPoint D s)
    (hrightsurj : ∀ P : Ideal ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))), P.IsMaximal →
      ((chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) (surfaceX O pi u a b) ∈ P → (∑ i : Fin (d+1), algebraMap
        (ConcreteSurface O pi u a b) ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) (c i) * ((chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)))^(d - i.val)) ∈
          P → ∃ s : D.ι ⊕ D.ιinf, rightPoint D s = P) :
    (∀ φ : AffineDirection ((IsLocalRing.ResidueField (ConcreteSurface O pi u a b))), φ ≠ zeroAffine ((IsLocalRing.ResidueField (ConcreteSurface O pi u a b))) → 0 < Dv (some φ) →
      ∃ i : D.ι, D.Q i = (directionPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b) e φ).map (algebraMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) (BlowupOverlap
          (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) ∧
    (0 < Dv (zeroDirection ((IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))) → Nonempty D.ι0) ∧
    (∀ l : D.ιinf, D.Pinf l = infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) ∧ Dv none = rightMultiplicity D (Sum.inr l)) ∧
    (0 < Dv none → Nonempty D.ιinf) := by sorry
