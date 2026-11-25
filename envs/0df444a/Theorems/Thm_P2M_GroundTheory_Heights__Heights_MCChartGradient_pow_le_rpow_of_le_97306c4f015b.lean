-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCChartGradient_pow_le_rpow_of_le_97306c4f015b
-- name    : P2M_GroundTheory_Heights__Heights_MCChartGradient_pow_le_rpow_of_le_97306c4f015b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:18.058883+00:00
-- url     : https://prove2.me/theorems/fe6e853f-c2ae-4b34-aaee-c7705ab6039e
-- title:
--   P2 M Ground Theory Heights  Heights MCChart Gradient pow le rpow of le 97306c4f015b: P2 M Ground Theory Heights  Heights MCChart Gradient pow le rpow of le 97306c4f015b
-- statement:
--   The P2 M Ground Theory Heights  Heights MCChart Gradient pow le rpow of le 97306c4f015b construction uses the P2 M Ground Theory Heights  Heights MCChart Gradient pow le rpow of le 97306c4f015b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartGradient.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartGradient.lean#L33-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartGradient
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
noncomputable section
open GroundTheory.Heights₂.Heights.MCChartGradient

theorem P2M_GroundTheory_Heights__Heights_MCChartGradient_pow_le_rpow_of_le_97306c4f015b {r C : ℝ} {k : ℕ} (hr : 1 ≤ r) (hk : (k : ℝ) ≤ C) :
    r ^ k ≤ r ^ C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCChartGradient».«pow_le_rpow_of_le» := P2M_GroundTheory_Heights__Heights_MCChartGradient_pow_le_rpow_of_le_97306c4f015b
