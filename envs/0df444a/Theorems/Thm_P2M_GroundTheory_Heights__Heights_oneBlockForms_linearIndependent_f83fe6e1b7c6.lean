-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_oneBlockForms_linearIndependent_f83fe6e1b7c6
-- name    : P2M_GroundTheory_Heights__Heights_oneBlockForms_linearIndependent_f83fe6e1b7c6
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:49:34.85161+00:00
-- url     : https://prove2.me/theorems/ffd9d532-c7cb-4e01-9329-581abe043b53
-- title:
--   P2 M Ground Theory Heights  Heights one Block Forms linear Independent f83fe6e1b7c6: P2 M Ground Theory Heights  Heights one Block Forms linear Independent f83fe6e1b7c6
-- statement:
--   The P2 M Ground Theory Heights  Heights one Block Forms linear Independent f83fe6e1b7c6 construction uses the P2 M Ground Theory Heights  Heights one Block Forms linear Independent f83fe6e1b7c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockStandard.lean#L41-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockStandard.lean#L41-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockStandard
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
open MvPolynomial NumberField Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_oneBlockForms_linearIndependent_f83fe6e1b7c6 {e r : ℕ} (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    LinearIndependent ℤ (oneBlockForms (r := r) om) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«oneBlockForms_linearIndependent» := P2M_GroundTheory_Heights__Heights_oneBlockForms_linearIndependent_f83fe6e1b7c6
