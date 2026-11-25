-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_VecAtNeZero_proof_8dea7b49204d
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_VecAtNeZero_proof_8dea7b49204d
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:44:29.386342+00:00
-- url     : https://prove2.me/theorems/a8c66cd9-6dd5-49d8-9e90-9594d57fac80
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Vec At Ne Zero proof 8dea7b49204d: P2 M Ground Theory Heights  Heights Finite Covolume Vec At Ne Zero proof 8dea7b49204d
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Vec At Ne Zero proof 8dea7b49204d construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Vec At Ne Zero proof 8dea7b49204d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVecAtNeZero.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVecAtNeZero.lean#L10-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVecAtNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Module NumberField
variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_VecAtNeZero_proof_8dea7b49204d (v : Basis ι E W) : VecAtNeZero.Statement v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«VecAtNeZero».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_VecAtNeZero_proof_8dea7b49204d
