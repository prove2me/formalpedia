-- Prove2me | Theorems.Thm_TypeDensity_concrete_single_state_eq_union_cells
-- name    : TypeDensity.concrete_single_state_eq_union_cells
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:09.552285+00:00
-- url     : https://prove2.me/theorems/75cdfde7-fdcc-4375-aea3-01f8e54b2464
-- title:
--   The single state set of the concrete surface is the disjoint union of the residue cells lifting the single residue ideals.
-- statement:
--   The single state set of the concrete surface is the disjoint union of the residue cells lifting the single residue ideals.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L930-L979

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Theorems.Thm_TypeDensity_concrete_surface_contact_eq_special_fiber_contact
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.concrete_single_state_eq_union_cells (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (u : (TwoSeries O)ˣ)
    (a : ℕ) (ha : 0 < a) [IsDomain (ConcreteSurface O pi u a 0)]
    [IsRegularLocalRing (ConcreteSurface O pi u a 0)]
    (S : SurfaceData O (ConcreteSurface O pi u a 0))
    (hSt : S.t = surfaceT O pi u a 0) (hSa : S.a = a) (hSb : S.b = 0)
    (e : (ConcreteSurface O pi u a 0 ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a 0)
    (he : ∀ s : TwoSeries O, e
      (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi})
        (surfaceMk O pi u a 0 s)) =
      Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a 0) (residueSeries O s))
    (c : ℕ) (hc : 0 < c)
    (F : singleResidueIdeals (IsLocalRing.ResidueField O) a c → ConcreteSurface O pi u a 0)
    (hF : ∀ I, Ideal.span
      {e ((Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi})) (F I))} =
      I.val) :
    surfaceStateSet O (ConcreteSurface O pi u a 0) S (State.single a c) =
    ⋃ I, residueIdealCell (algebraMap O (ConcreteSurface O pi u a 0) pi) (F I) ∧
    Pairwise
    (fun I J ↦ Disjoint (residueIdealCell (algebraMap O (ConcreteSurface O pi u a 0) pi) (F I))
      (residueIdealCell (algebraMap O (ConcreteSurface O pi u a 0) pi) (F J))) := by sorry
