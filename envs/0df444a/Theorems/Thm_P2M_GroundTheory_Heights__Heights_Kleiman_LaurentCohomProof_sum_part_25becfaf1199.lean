-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_sum_part_25becfaf1199
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_sum_part_25becfaf1199
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:51.091802+00:00
-- url     : https://prove2.me/theorems/89218607-6bc0-4c86-9481-4a031718cc92
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof sum part 25becfaf1199: P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof sum part 25becfaf1199
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof sum part 25becfaf1199 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Cohom Proof sum part 25becfaf1199 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean#L32-L37

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_sum_part_25becfaf1199 (f : Laurent S N) : ∑ J, part S J f = f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentCohomProof».«sum_part» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_sum_part_25becfaf1199
