-- Prove2me | Theorems.Thm_TypeDensity_hensel_pair_exists
-- name    : TypeDensity.hensel_pair_exists
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T12:53:38.30847+00:00
-- url     : https://prove2.me/theorems/ad5d8363-3211-4138-a008-40e7c656bf9f
-- title:
--   Hensel's lemma: over a complete local ring, a coprime monic factorization `g * h` of the residue reduction of a monic `F` lifts to a monic factorization `F = G * H` with the same degrees.
-- statement:
--   Hensel's lemma: over a complete local ring, a coprime monic factorization `g * h` of the residue reduction of a monic `F` lifts to a monic factorization `F = G * H` with the same degrees.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L515-L524

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
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
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.hensel_pair_exists (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (F : Polynomial O) (hF : F.Monic)
    (g h : Polynomial (IsLocalRing.ResidueField O)) (hg : g.Monic) (hh : h.Monic)
    (hc : IsCoprime g h) (hred : F.map (IsLocalRing.residue O) = g * h) :
    ∃ G H : Polynomial O, G.Monic ∧ H.Monic ∧ F=G*H ∧ G.map (IsLocalRing.residue O)=g ∧
      H.map (IsLocalRing.residue O)=h ∧ G.natDegree=g.natDegree ∧ H.natDegree=h.natDegree := by sorry
