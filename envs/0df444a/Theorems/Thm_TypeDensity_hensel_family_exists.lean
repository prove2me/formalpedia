-- Prove2me | Theorems.Thm_TypeDensity_hensel_family_exists
-- name    : TypeDensity.hensel_family_exists
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:20.179391+00:00
-- url     : https://prove2.me/theorems/c1750aea-d62a-49d9-95d6-d5bf36e943fa
-- title:
--   Hensel's lemma for finitely many pairwise coprime monic residue factors.
-- statement:
--   Hensel's lemma holds for finitely many pairwise coprime monic residue factors.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L526-L567

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Theorems.Thm_TypeDensity_hensel_pair_exists
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

theorem TypeDensity.hensel_family_exists (O ι : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Fintype ι] (F : Polynomial O) (hF : F.Monic)
    (g : ι → Polynomial (IsLocalRing.ResidueField O)) (hg : ∀ i, (g i).Monic)
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (hred : F.map (IsLocalRing.residue O) = ∏ i, g i) :
    ∃ G : ι→Polynomial O, (∀ i, (G i).Monic) ∧ F=∏ i, G i ∧
      (∀ i, (G i).map (IsLocalRing.residue O)=g i) ∧ (∀ i, (G i).natDegree=(g i).natDegree) := by sorry
