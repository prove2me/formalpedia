-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCChartFrameDeriv_le_one_add_sum_6f37569901f6
-- name    : P2M_GroundTheory_Heights__Heights_MCChartFrameDeriv_le_one_add_sum_6f37569901f6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:05.30473+00:00
-- url     : https://prove2.me/theorems/85ef56fd-3826-45e5-b771-75bfc0d49c34
-- title:
--   P2 M Ground Theory Heights  Heights MCChart Frame Deriv le one add sum 6f37569901f6: P2 M Ground Theory Heights  Heights MCChart Frame Deriv le one add sum 6f37569901f6
-- statement:
--   The P2 M Ground Theory Heights  Heights MCChart Frame Deriv le one add sum 6f37569901f6 construction uses the P2 M Ground Theory Heights  Heights MCChart Frame Deriv le one add sum 6f37569901f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartFrameDeriv.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartFrameDeriv.lean#L12-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartFrameDeriv
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
noncomputable section
open GroundTheory.Heights₂.Heights.MCChartFrameDeriv

theorem P2M_GroundTheory_Heights__Heights_MCChartFrameDeriv_le_one_add_sum_6f37569901f6 {g r : ℕ} (A : Fin g → Fin r → ℝ) (hA : ∀ j l, 0 < A j l) (j : Fin g)
    (l : Fin r) : A j l ≤ 1 + ∑ j', ∑ l', A j' l' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCChartFrameDeriv».«le_one_add_sum» := P2M_GroundTheory_Heights__Heights_MCChartFrameDeriv_le_one_add_sum_6f37569901f6
