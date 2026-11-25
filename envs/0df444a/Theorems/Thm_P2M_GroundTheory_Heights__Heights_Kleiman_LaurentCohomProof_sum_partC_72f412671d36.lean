-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_sum_partC_72f412671d36
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_sum_partC_72f412671d36
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:19.644071+00:00
-- url     : https://prove2.me/theorems/de0fab3e-83ee-4f62-947a-89beac85135f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof sum part C 72f412671d36: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof sum part C 72f412671d36
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof sum part C 72f412671d36 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof sum part C 72f412671d36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L104-L107

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_sum_partC_72f412671d36 (i : ℕ) (z : Cech.Cochain (G S N) i) : ∑ J, partC S J i z = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«sum_partC» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_sum_partC_72f412671d36
