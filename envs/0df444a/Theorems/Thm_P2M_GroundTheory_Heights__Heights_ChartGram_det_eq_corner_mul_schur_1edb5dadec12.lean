-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_det_eq_corner_mul_schur_1edb5dadec12
-- name    : P2M_GroundTheory_Heights__Heights_ChartGram_det_eq_corner_mul_schur_1edb5dadec12
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:32.034731+00:00
-- url     : https://prove2.me/theorems/522854a0-b8a7-4e06-be2e-2a66c7e6aee4
-- title:
--   P2 M Ground Theory Heights  Heights Chart Gram det eq corner mul schur 1edb5dadec12: P2 M Ground Theory Heights  Heights Chart Gram det eq corner mul schur 1edb5dadec12
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Gram det eq corner mul schur 1edb5dadec12 construction uses the P2 M Ground Theory Heights  Heights Chart Gram det eq corner mul schur 1edb5dadec12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramSchur.lean#L8-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramSchur.lean#L8-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramSchur
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights

theorem P2M_GroundTheory_Heights__Heights_ChartGram_det_eq_corner_mul_schur_1edb5dadec12 {K : Type*} [Field K] {e : ℕ}
    (M : Matrix (Fin (e + 1)) (Fin (e + 1)) K) (h : M 0 0 ≠ 0) :
    M.det = M 0 0 *
      (Matrix.of fun i j : Fin e => M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartGram».«det_eq_corner_mul_schur» := P2M_GroundTheory_Heights__Heights_ChartGram_det_eq_corner_mul_schur_1edb5dadec12
