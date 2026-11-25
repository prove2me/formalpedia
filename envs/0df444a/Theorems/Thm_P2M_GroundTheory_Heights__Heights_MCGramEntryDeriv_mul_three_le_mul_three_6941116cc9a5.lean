-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_mul_three_le_mul_three_6941116cc9a5
-- name    : P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_mul_three_le_mul_three_6941116cc9a5
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:15.933917+00:00
-- url     : https://prove2.me/theorems/87010165-e8e0-4747-b1a7-5f323b666812
-- title:
--   P2 M Ground Theory Heights  Heights MCGram Entry Deriv mul three le mul three 6941116cc9a5: P2 M Ground Theory Heights  Heights MCGram Entry Deriv mul three le mul three 6941116cc9a5
-- statement:
--   The P2 M Ground Theory Heights  Heights MCGram Entry Deriv mul three le mul three 6941116cc9a5 construction uses the P2 M Ground Theory Heights  Heights MCGram Entry Deriv mul three le mul three 6941116cc9a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramEntryDeriv.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramEntryDeriv.lean#L42-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramEntryDeriv
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
open Matrix
open GroundTheory.Heights₂.Heights.MCGramEntryDeriv
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_mul_three_le_mul_three_6941116cc9a5 {x y z X Y W : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hx : x ≤ X)
    (hy : y ≤ Y) (hz : z ≤ W) : x * y * z ≤ X * Y * W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCGramEntryDeriv».«mul_three_le_mul_three» := P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_mul_three_le_mul_three_6941116cc9a5
