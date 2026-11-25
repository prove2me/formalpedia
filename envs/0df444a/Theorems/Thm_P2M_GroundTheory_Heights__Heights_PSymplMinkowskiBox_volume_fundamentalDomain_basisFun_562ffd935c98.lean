-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_volume_fundamentalDomain_basisFun_562ffd935c98
-- name    : P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_volume_fundamentalDomain_basisFun_562ffd935c98
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:32.444208+00:00
-- url     : https://prove2.me/theorems/2aa44475-b0da-4b85-be6e-a7fc01688ac2
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Minkowski Box volume fundamental Domain basis Fun 562ffd935c98: P2 M Ground Theory Heights  Heights PSympl Minkowski Box volume fundamental Domain basis Fun
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Minkowski Box volume fundamental Domain basis Fun 562ffd935c98 construction uses the P2 M Ground Theory Heights  Heights PSympl Minkowski Box volume fundamental Domain basis Fun 562ffd935c98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinkowskiBox.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinkowskiBox.lean#L30-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinkowskiBox
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
open Matrix MeasureTheory
open GroundTheory.Heights₂.Heights.PSymplMinkowskiBox

theorem P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_volume_fundamentalDomain_basisFun_562ffd935c98 (ι : Type) [Fintype ι] :
    volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplMinkowskiBox».«volume_fundamentalDomain_basisFun» := P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_volume_fundamentalDomain_basisFun_562ffd935c98
