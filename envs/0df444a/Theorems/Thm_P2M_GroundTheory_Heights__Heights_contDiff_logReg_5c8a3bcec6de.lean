-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de
-- name    : P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:12.979805+00:00
-- url     : https://prove2.me/theorems/057baad3-e2f7-4827-986e-6a18680fb31d
-- title:
--   P2 M Ground Theory Heights  Heights cont Diff log Reg 5c8a3bcec6de: P2 M Ground Theory Heights  Heights cont Diff log Reg 5c8a3bcec6de
-- statement:
--   The P2 M Ground Theory Heights  Heights cont Diff log Reg 5c8a3bcec6de construction uses the P2 M Ground Theory Heights  Heights cont Diff log Reg 5c8a3bcec6de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLelongRegularise.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLelongRegularise.lean#L21-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
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
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (logReg u ε) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«contDiff_logReg» := P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de
