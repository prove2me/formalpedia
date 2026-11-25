-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_specFirst_eq_map_eval_e6fa4097f9e8
-- name    : P2M_GroundTheory_Heights__Heights_specFirst_eq_map_eval_e6fa4097f9e8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:17.066972+00:00
-- url     : https://prove2.me/theorems/346c909d-6741-4a15-9471-c7c56d03e5b7
-- title:
--   P2 M Ground Theory Heights  Heights spec First eq map eval e6fa4097f9e8: P2 M Ground Theory Heights  Heights spec First eq map eval e6fa4097f9e8
-- statement:
--   The P2 M Ground Theory Heights  Heights spec First eq map eval e6fa4097f9e8 construction uses the P2 M Ground Theory Heights  Heights spec First eq map eval e6fa4097f9e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PSpecFirstNe.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PSpecFirstNe.lean#L22-L35

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

theorem P2M_GroundTheory_Heights__Heights_specFirst_eq_map_eval_e6fa4097f9e8 (g : MvPolynomial (Fin (k + 1) × Fin n) F) (t : Fin n → F) :
    specFirst g t = map (eval t) (sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit g)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«specFirst_eq_map_eval» := P2M_GroundTheory_Heights__Heights_specFirst_eq_map_eval_e6fa4097f9e8
