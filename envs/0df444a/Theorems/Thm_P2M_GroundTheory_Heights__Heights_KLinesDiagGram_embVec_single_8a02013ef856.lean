-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesDiagGram_embVec_single_8a02013ef856
-- name    : P2M_GroundTheory_Heights__Heights_KLinesDiagGram_embVec_single_8a02013ef856
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:33.844806+00:00
-- url     : https://prove2.me/theorems/d30072c5-7ba8-463f-83bd-0de5a116c571
-- title:
--   P2 M Ground Theory Heights  Heights KLines Diag Gram emb Vec single 8a02013ef856: P2 M Ground Theory Heights  Heights KLines Diag Gram emb Vec single 8a02013ef856
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Diag Gram emb Vec single 8a02013ef856 construction uses the P2 M Ground Theory Heights  Heights KLines Diag Gram emb Vec single 8a02013ef856 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesDiagGram.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesDiagGram.lean#L9-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesDiagGram
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
open GroundTheory.Heights₂.Heights.KLinesDiagGram

theorem P2M_GroundTheory_Heights__Heights_KLinesDiagGram_embVec_single_8a02013ef856 {K : Type*} [Field K] (σ : K →+* ℂ) {n : ℕ} (x : Fin n) :
    embVec σ (Pi.single x 1 : Fin n → K) = Pi.single x 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesDiagGram».«embVec_single» := P2M_GroundTheory_Heights__Heights_KLinesDiagGram_embVec_single_8a02013ef856
