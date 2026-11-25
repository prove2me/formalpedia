-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_sheetSum_mono_8368eee2d608
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_sheetSum_mono_8368eee2d608
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:26.615811+00:00
-- url     : https://prove2.me/theorems/a2055b9f-a43f-4ed2-9c8d-67cfff0988af
-- title:
--   P2 M Ground Theory Heights  Heights Chart Int Count Add sheet Sum mono 8368eee2d608: P2 M Ground Theory Heights  Heights Chart Int Count Add sheet Sum mono 8368eee2d608
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Int Count Add sheet Sum mono 8368eee2d608 construction uses the P2 M Ground Theory Heights  Heights Chart Int Count Add sheet Sum mono 8368eee2d608 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L66-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntCountAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartIntCountAdd
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
open GroundTheory.Heights₂.Heights.ChartIntCountAdd
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_sheetSum_mono_8368eee2d608 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ}
    (hFG : ∀ x s, F x s ≤ G x s) : sheetSum J A F y ≤ sheetSum J A G y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntCountAdd».«sheetSum_mono» := P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_sheetSum_mono_8368eee2d608
