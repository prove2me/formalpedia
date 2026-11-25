-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_specFirst_ne_zero_e3165fe98c76
-- name    : P2M_GroundTheory_Heights__Heights_exists_specFirst_ne_zero_e3165fe98c76
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:56.488801+00:00
-- url     : https://prove2.me/theorems/757f74d7-b0fb-4e7b-823f-0ca724e51e18
-- title:
--   P2 M Ground Theory Heights  Heights exists spec First ne zero e3165fe98c76: P2 M Ground Theory Heights  Heights exists spec First ne zero e3165fe98c76
-- statement:
--   The P2 M Ground Theory Heights  Heights exists spec First ne zero e3165fe98c76 construction uses the P2 M Ground Theory Heights  Heights exists spec First ne zero e3165fe98c76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PSpecFirstNe.lean#L37-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PSpecFirstNe.lean#L37-L51

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

theorem P2M_GroundTheory_Heights__Heights_exists_specFirst_ne_zero_e3165fe98c76 [Infinite F] {f : MvPolynomial (Fin (k + 1) × Fin n) F} (hf : f ≠ 0) :
    ∃ t : Fin n → F, specFirst f t ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_specFirst_ne_zero» := P2M_GroundTheory_Heights__Heights_exists_specFirst_ne_zero_e3165fe98c76
