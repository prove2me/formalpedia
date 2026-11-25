-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_not_faceOK_of_card_one_ac09a1e47140
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_not_faceOK_of_card_one_ac09a1e47140
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:56.329799+00:00
-- url     : https://prove2.me/theorems/1348327b-5cb5-4e03-bfc1-e3294921dbf3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic not face OK of card one ac09a1e47140: P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic not face OK of card one ac09a1e47140
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic not face OK of card one ac09a1e47140 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic not face OK of card one ac09a1e47140 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L48-L52

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_not_faceOK_of_card_one_ac09a1e47140 {J : ∀ k, Finset (ι k)} {n : ℕ} (A : ∀ k, Finset (ι k)) (l : K) {i : ι l}
    (hi : i ∈ A l) (h : (A l).card = 1) : ¬ FaceOK J n (Function.update A l ((A l).erase i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombCyclic».«not_faceOK_of_card_one» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_not_faceOK_of_card_one_ac09a1e47140
