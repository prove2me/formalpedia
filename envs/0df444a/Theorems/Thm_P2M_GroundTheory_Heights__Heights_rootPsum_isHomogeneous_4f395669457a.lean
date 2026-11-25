-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_rootPsum_isHomogeneous_4f395669457a
-- name    : P2M_GroundTheory_Heights__Heights_rootPsum_isHomogeneous_4f395669457a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:55.919144+00:00
-- url     : https://prove2.me/theorems/78e3da49-cdf8-4c24-90c0-cf9fe73682fa
-- title:
--   P2 M Ground Theory Heights  Heights root Psum is Homogeneous 4f395669457a: P2 M Ground Theory Heights  Heights root Psum is Homogeneous 4f395669457a
-- statement:
--   The P2 M Ground Theory Heights  Heights root Psum is Homogeneous 4f395669457a construction uses the P2 M Ground Theory Heights  Heights root Psum is Homogeneous 4f395669457a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutIKillsIdeal.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutIKillsIdeal.lean#L9-L11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutIKillsIdeal
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

theorem P2M_GroundTheory_Heights__Heights_rootPsum_isHomogeneous_4f395669457a (f j k m : ℕ) (τ : Fin f) :
    (rootPsum f j k m τ).IsHomogeneous m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«rootPsum_isHomogeneous» := P2M_GroundTheory_Heights__Heights_rootPsum_isHomogeneous_4f395669457a
