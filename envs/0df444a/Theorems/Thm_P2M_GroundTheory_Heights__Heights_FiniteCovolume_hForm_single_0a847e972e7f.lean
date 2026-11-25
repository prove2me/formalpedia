-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_single_0a847e972e7f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_single_0a847e972e7f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:08.893391+00:00
-- url     : https://prove2.me/theorems/72a30abd-86d9-5100-a3c6-1df298c25efb
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume h Form single 0a847e972e7f: P2 M Ground Theory Heights  Heights Finite Covolume h Form single 0a847e972e7f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume h Form single 0a847e972e7f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume h Form single 0a847e972e7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L67-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable (H : Matrix ι ι ℂ)
variable [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_single_0a847e972e7f (X : Matrix ι ι ℂ) (i j : ι) :
    hForm X (Pi.single i 1) (Pi.single j 1) = X i j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«hForm_single» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_single_0a847e972e7f
