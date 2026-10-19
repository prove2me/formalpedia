-- Prove2me | Theorems.Thm_TypeDensity_concrete_crossing_state_eq_union_cells
-- name    : TypeDensity.concrete_crossing_state_eq_union_cells
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:19.462655+00:00
-- url     : https://prove2.me/theorems/dfd2f1c8-099b-48bd-8dde-f0ae723276e9
-- title:
--   The crossing state set of the concrete surface is the disjoint union of the residue cells lifting the crossing residue ideals.
-- statement:
--   The crossing state set of the concrete surface is the disjoint union of the residue cells lifting the crossing residue ideals.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L871-L928

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

theorem TypeDensity.concrete_crossing_state_eq_union_cells (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b))
    (hSt : S.t = surfaceT O pi u a b) (hSx : S.x = surfaceX O pi u a b) (hSa : S.a = a)
    (hSb : S.b = b)
    (e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a b)
    (he : ∀ s : TwoSeries O, e
      (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
        (surfaceMk O pi u a b s)) =
      Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a b) (residueSeries O s))
    (c h : ℕ) (hc : 0 < c) (hh : 0 < h)
    (F : crossingResidueIdeals (IsLocalRing.ResidueField O) a b c h → ConcreteSurface O pi u a b)
    (hF : ∀ I, Ideal.span
      {e ((Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})) (F I))} =
      I.val) :
    surfaceStateSet O (ConcreteSurface O pi u a b) S (State.crossing a b c h) =
    ⋃ I, residueIdealCell (algebraMap O (ConcreteSurface O pi u a b) pi) (F I) ∧
    Pairwise
    (fun I J ↦ Disjoint (residueIdealCell (algebraMap O (ConcreteSurface O pi u a b) pi) (F I))
      (residueIdealCell (algebraMap O (ConcreteSurface O pi u a b) pi) (F J))) := by sorry
