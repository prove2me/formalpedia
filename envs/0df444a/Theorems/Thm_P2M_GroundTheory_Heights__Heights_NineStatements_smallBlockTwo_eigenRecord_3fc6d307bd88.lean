-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_smallBlockTwo_eigenRecord_3fc6d307bd88
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_smallBlockTwo_eigenRecord_3fc6d307bd88
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:43.359539+00:00
-- url     : https://prove2.me/theorems/9cbd5951-e5ee-4e48-a800-6b7aa01bd3f1
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements small Block Two eigen Record 3fc6d307bd88: P2 M Ground Theory Heights  Heights Nine Statements small Block Two eigen Record 3fc6d307bd88
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements small Block Two eigen Record 3fc6d307bd88 construction uses the P2 M Ground Theory Heights  Heights Nine Statements small Block Two eigen Record 3fc6d307bd88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L134-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L134-L140

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem P2M_GroundTheory_Heights__Heights_NineStatements_smallBlockTwo_eigenRecord_3fc6d307bd88 {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
    (ι : E →+* L) {j' : ℕ} (hj : 1 ≤ j') : EigenRecordAt (fun _ => ι) j' (smallBlockTwo ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«smallBlockTwo_eigenRecord» := P2M_GroundTheory_Heights__Heights_NineStatements_smallBlockTwo_eigenRecord_3fc6d307bd88
