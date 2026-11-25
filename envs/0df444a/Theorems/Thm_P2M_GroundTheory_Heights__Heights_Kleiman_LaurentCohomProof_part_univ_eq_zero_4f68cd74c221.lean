-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_univ_eq_zero_4f68cd74c221
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_univ_eq_zero_4f68cd74c221
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:42.572805+00:00
-- url     : https://prove2.me/theorems/8bd57ae4-c9a4-4e3d-931d-c19019a71bdf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part univ eq zero 4f68cd74c221: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part univ eq zero 4f68cd74c221
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part univ eq zero 4f68cd74c221 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof part univ eq zero 4f68cd74c221 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L138-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L138-L148

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
variable {S : Type u} [CommRing S] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_univ_eq_zero_4f68cd74c221 {c : ℤ} (hc : 0 ≤ c) {I : StdCell N} {f : Laurent S N}
    (hf : f ∈ laurentDeg S N c I) : part S Finset.univ f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«part_univ_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_univ_eq_zero_4f68cd74c221
