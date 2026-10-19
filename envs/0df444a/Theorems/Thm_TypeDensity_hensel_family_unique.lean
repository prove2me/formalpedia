-- Prove2me | Theorems.Thm_TypeDensity_hensel_family_unique
-- name    : TypeDensity.hensel_family_unique
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:03.549142+00:00
-- url     : https://prove2.me/theorems/960ca664-56d3-4db5-b3b5-bc3966fae23c
-- title:
--   Over a local ring, a factorization into monic factors with pairwise coprime reductions is determined by the reductions.
-- statement:
--   Over a local ring, a factorization into monic factors with pairwise coprime reductions is determined by the reductions.
-- source:
--   TypeDensity/Unramified/Extension.lean#L970-L1001

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Theorems.Thm_TypeDensity_hensel_pair_unique
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
set_option autoImplicit false

open TypeDensity
open Polynomial IsLocalRing MeasureTheory

theorem TypeDensity.hensel_family_unique (O ι : Type) [CommRing O] [IsLocalRing O] [Fintype ι]
    (G G' : ι → Polynomial O) (hG : ∀ i, (G i).Monic) (hG' : ∀ i, (G' i).Monic)
    (hred : ∀ i, (G i).map (IsLocalRing.residue O) = (G' i).map (IsLocalRing.residue O))
    (hc : ∀ i j, i ≠ j → IsCoprime ((G i).map (IsLocalRing.residue O))
      ((G j).map (IsLocalRing.residue O))) (hp : ∏ i, G i = ∏ i, G' i) :
    G = G' := by sorry
