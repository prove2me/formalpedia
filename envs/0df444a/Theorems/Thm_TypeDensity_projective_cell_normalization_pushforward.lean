-- Prove2me | Theorems.Thm_TypeDensity_projective_cell_normalization_pushforward
-- name    : TypeDensity.projective_cell_normalization_pushforward
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:43:26.160001+00:00
-- url     : https://prove2.me/theorems/d815c835-977b-46c2-a694-d0fcce83b91a
-- title:
--   Normalizing a primitive vector at a coordinate `μ` with `G μ = 1` maps the projective cell of `G` onto the reduced form cell of `G`, with fibres the unit multiples, and pushes the normaliz
-- statement:
--   Normalizing a primitive vector at a coordinate `μ` with `G μ = 1` maps the projective cell of `G` onto the reduced form cell of `G`, with fibres the unit multiples, and pushes the normalized projective cell measure forward to the normalized reduced form cell measure.
-- source:
--   TypeDensity/Unramified/HomogeneousCells.lean#L694-L779

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_finite_coordinate_adic_congruence
import Theorems.Thm_TypeDensity_finite_coordinate_borel_cylinders
import Theorems.Thm_TypeDensity_finite_quotient_event_mass
import Theorems.Thm_TypeDensity_residue_quotient_card
import Theorems.Thm_TypeDensity_coefficient_measure_probability
import Theorems.Thm_TypeDensity_normalized_form_cell_cylinder_mass
import Theorems.Thm_TypeDensity_projective_cell_mass
import Theorems.Thm_TypeDensity_measurePreserving_cellMeasure_of_balls
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.projective_cell_normalization_pushforward (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (G : Fin (n + 1) → IsLocalRing.ResidueField O) (μ : Fin (n + 1)) (hGμ : G μ = 1) :
    Set.MapsTo (projectiveNormalize O n G μ) (projectiveCell O n G) (reducedFormCell O n μ G) ∧
    Set.SurjOn (projectiveNormalize O n G μ) (projectiveCell O n G) (reducedFormCell O n μ G) ∧
    (∀ a ∈ projectiveCell O n G, ∀ a' ∈ projectiveCell O n G,
      projectiveNormalize O n G μ a = projectiveNormalize O n G μ a' ↔
        ∃ u : Oˣ, a' = (u : O) • a) ∧
    MeasureTheory.MeasurePreserving (projectiveNormalize O n G μ)
      (cellMeasure O (n+1) (projectiveCell O n G)) (cellMeasure O n (reducedFormCell O n μ G)) := by sorry
