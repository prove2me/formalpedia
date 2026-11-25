-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_specFirstSplit_injective_40cd8caf3b1a
-- name    : P2M_GroundTheory_Heights__Heights_specFirstSplit_injective_40cd8caf3b1a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:20.257519+00:00
-- url     : https://prove2.me/theorems/efe5d5eb-5b32-4afe-9cd8-25da17e8f010
-- title:
--   P2 M Ground Theory Heights  Heights spec First Split injective 40cd8caf3b1a: P2 M Ground Theory Heights  Heights spec First Split injective 40cd8caf3b1a
-- statement:
--   The P2 M Ground Theory Heights  Heights spec First Split injective 40cd8caf3b1a construction uses the P2 M Ground Theory Heights  Heights spec First Split injective 40cd8caf3b1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PSpecFirstNe.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PSpecFirstNe.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PSpecFirstNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {F : Type} [Field F] {k n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_specFirstSplit_injective_40cd8caf3b1a : Function.Injective (specFirstSplit (k := k) (n := n)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«specFirstSplit_injective» := P2M_GroundTheory_Heights__Heights_specFirstSplit_injective_40cd8caf3b1a
