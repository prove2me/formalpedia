-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlueckerNormSqAlt_rowsOf_conjTranspose_e6b7b0baa3b1
-- name    : P2M_GroundTheory_Heights__Heights_PlueckerNormSqAlt_rowsOf_conjTranspose_e6b7b0baa3b1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:26.869839+00:00
-- url     : https://prove2.me/theorems/6d553db7-0ce2-598e-9fcf-1bb16768031d
-- title:
--   P2 M Ground Theory Heights  Heights Pluecker Norm Sq Alt rows Of conj Transpose e6b7b0baa3b1: P2 M Ground Theory Heights  Heights Pluecker Norm Sq Alt rows Of conj Transpose e6b7b0baa3b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Pluecker Norm Sq Alt rows Of conj Transpose e6b7b0baa3b1 construction uses the P2 M Ground Theory Heights  Heights Pluecker Norm Sq Alt rows Of conj Transpose e6b7b0baa3b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPlueckerNormSq.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPlueckerNormSq.lean#L25-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPlueckerNormSq
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
open Matrix Finset
noncomputable section
open GroundTheory.Heights₂.Heights.PlueckerNormSqAlt

theorem P2M_GroundTheory_Heights__Heights_PlueckerNormSqAlt_rowsOf_conjTranspose_e6b7b0baa3b1 {j N : ℕ} (A : Matrix (Fin j) (Fin N) ℂ)
    (I : {I : Finset (Fin N) // I.card = j}) : rowsOf Aᴴ I = (colsOf A I)ᴴ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PlueckerNormSqAlt».«rowsOf_conjTranspose» := P2M_GroundTheory_Heights__Heights_PlueckerNormSqAlt_rowsOf_conjTranspose_e6b7b0baa3b1
