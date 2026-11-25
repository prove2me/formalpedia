-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_absNorm_extDifferent_0c7e900f3013
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_absNorm_extDifferent_0c7e900f3013
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:05:10.268151+00:00
-- url     : https://prove2.me/theorems/aed09dbf-694b-4ec2-8fe3-85280755e2bd
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements abs Norm ext Different 0c7e900f3013: P2 M Ground Theory Heights  Heights Nine Statements abs Norm ext Different 0c7e900f3013
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements abs Norm ext Different 0c7e900f3013 construction uses the P2 M Ground Theory Heights  Heights Nine Statements abs Norm ext Different 0c7e900f3013 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PDifferentExtNorm.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PDifferentExtNorm.lean#L9-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PDifferentExtNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField

theorem P2M_GroundTheory_Heights__Heights_NineStatements_absNorm_extDifferent_0c7e900f3013 {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    letI : Algebra E L := ι.toAlgebra
    Ideal.absNorm (extDifferent ι) = (discr E).natAbs ^ Module.finrank E L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«absNorm_extDifferent» := P2M_GroundTheory_Heights__Heights_NineStatements_absNorm_extDifferent_0c7e900f3013
