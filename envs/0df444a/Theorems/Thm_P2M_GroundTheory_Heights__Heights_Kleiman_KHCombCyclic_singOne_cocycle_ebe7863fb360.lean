-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_singOne_cocycle_ebe7863fb360
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_singOne_cocycle_ebe7863fb360
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:15.623371+00:00
-- url     : https://prove2.me/theorems/6a4ae1ae-ff91-4766-b769-757c573cbd14
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic sing One cocycle ebe7863fb360: P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic sing One cocycle ebe7863fb360
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic sing One cocycle ebe7863fb360 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic sing One cocycle ebe7863fb360 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L124-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L124-L162

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombCyclicSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
open Classical

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_singOne_cocycle_ebe7863fb360 (J : ∀ k, Finset (ι k)) (n : ℕ) (hJ : ∀ k, J k = ∅ ∨ J k = Finset.univ) :
    combD S J n (singOne S J n) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombCyclic».«singOne_cocycle» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_singOne_cocycle_ebe7863fb360
