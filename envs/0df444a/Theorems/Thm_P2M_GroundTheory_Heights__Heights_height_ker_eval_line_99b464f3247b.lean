-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_ker_eval_line_99b464f3247b
-- name    : P2M_GroundTheory_Heights__Heights_height_ker_eval_line_99b464f3247b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:54.122981+00:00
-- url     : https://prove2.me/theorems/f276d35b-782a-4473-819b-5e26446022d4
-- title:
--   P2 M Ground Theory Heights  Heights height ker eval line 99b464f3247b: P2 M Ground Theory Heights  Heights height ker eval line 99b464f3247b
-- statement:
--   The P2 M Ground Theory Heights  Heights height ker eval line 99b464f3247b construction uses the P2 M Ground Theory Heights  Heights height ker eval line 99b464f3247b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveNormalisationLength.lean#L65-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveNormalisationLength.lean#L65-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_height_ker_eval_line_99b464f3247b : (RingHom.ker (eval (0 : Fin 1 → ℂ))).height = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«height_ker_eval_line» := P2M_GroundTheory_Heights__Heights_height_ker_eval_line_99b464f3247b
