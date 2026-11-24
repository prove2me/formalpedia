-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fsLogReg_tendsto_8f83a55b2a2e
-- name    : P2M_GroundTheory_Heights__Heights_fsLogReg_tendsto_8f83a55b2a2e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:54.125384+00:00
-- url     : https://prove2.me/theorems/527d4e39-7b80-4c79-89de-dd13221b202e
-- title:
--   P2 M Ground Theory Heights  Heights fs Log Reg tendsto 8f83a55b2a2e: P2 M Ground Theory Heights  Heights fs Log Reg tendsto 8f83a55b2a2e
-- statement:
--   The P2 M Ground Theory Heights  Heights fs Log Reg tendsto 8f83a55b2a2e construction uses the P2 M Ground Theory Heights  Heights fs Log Reg tendsto 8f83a55b2a2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsGreenReg.lean#L25-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsGreenReg.lean#L25-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_fsLogReg_tendsto_8f83a55b2a2e (h : HermNorm n) (u y : Fin n → ℂ) (hy : 0 < h.dualNorm y)
    (hu : ∑ j, u j * y j ≠ 0) :
    Tendsto (fun ε => fsLogReg h u ε y) (𝓝 0) (𝓝 (fsLog h u y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fsLogReg_tendsto» := P2M_GroundTheory_Heights__Heights_fsLogReg_tendsto_8f83a55b2a2e
