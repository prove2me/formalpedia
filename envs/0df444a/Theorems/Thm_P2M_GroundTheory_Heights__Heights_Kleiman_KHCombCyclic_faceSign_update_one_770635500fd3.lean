-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceSign_update_one_770635500fd3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceSign_update_one_770635500fd3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:14.598303+00:00
-- url     : https://prove2.me/theorems/9d9e8507-1116-50e1-a61f-a73d2567083f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic face Sign update one 770635500fd3: P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic face Sign update one 770635500fd3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic face Sign update one 770635500fd3 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic face Sign update one 770635500fd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L79-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L79-L89

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceSign_update_one_770635500fd3 (A : ∀ k, Finset (ι k)) {k l : K} (hl : l ≠ k) (i : ι l) (v : Finset (ι k))
    (hA : (A k).card = 1) (hv : v.card = 1) :
    KH.faceSign (Function.update A k v) l i = KH.faceSign A l i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombCyclic».«faceSign_update_one» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceSign_update_one_770635500fd3
