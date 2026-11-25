-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarMassNearSmall_abs_sheetSum_le_e119edd687e0
-- name    : P2M_GroundTheory_Heights__Heights_VarMassNearSmall_abs_sheetSum_le_e119edd687e0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:41:47.270157+00:00
-- url     : https://prove2.me/theorems/4d2eadd3-1837-489c-9557-9acccf14ae97
-- title:
--   P2 M Ground Theory Heights  Heights Var Mass Near Small abs sheet Sum le e119edd687e0: P2 M Ground Theory Heights  Heights Var Mass Near Small abs sheet Sum le e119edd687e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Var Mass Near Small abs sheet Sum le e119edd687e0 construction uses the P2 M Ground Theory Heights  Heights Var Mass Near Small abs sheet Sum le e119edd687e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarMassNearSmall.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarMassNearSmall.lean#L21-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarMassNearSmall
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
open scoped ENNReal NNReal
noncomputable section
open GroundTheory.Heights₂.Heights.VarMassNearSmall
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_VarMassNearSmall_abs_sheetSum_le_e119edd687e0 (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ} (hFG : ∀ x s, |F x s| ≤ G x s)
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    |sheetSum J A F y| ≤ sheetSum J A G y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarMassNearSmall».«abs_sheetSum_le» := P2M_GroundTheory_Heights__Heights_VarMassNearSmall_abs_sheetSum_le_e119edd687e0
