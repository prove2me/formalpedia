-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceSign_pair_b9b696b63fc2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceSign_pair_b9b696b63fc2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:31.363272+00:00
-- url     : https://prove2.me/theorems/4b16a2ee-79f5-4d57-8dad-3309c1b850a8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic face Sign pair b9b696b63fc2: P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic face Sign pair b9b696b63fc2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic face Sign pair b9b696b63fc2 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic face Sign pair b9b696b63fc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L54-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L54-L77

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceSign_pair_b9b696b63fc2 (A : ∀ k, Finset (ι k)) (k : K) {a b : ι k} (hab : a < b) (he : A k = {a, b}) :
    KH.faceSign A k b = - KH.faceSign A k a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombCyclic».«faceSign_pair» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceSign_pair_b9b696b63fc2
