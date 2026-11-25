-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarMassNearSmall_proof_c377500c093c
-- name    : P2M_GroundTheory_Heights__Heights_VarMassNearSmall_proof_c377500c093c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:25.673824+00:00
-- url     : https://prove2.me/theorems/9173861f-e68d-4820-b601-5298729873d5
-- title:
--   P2 M Ground Theory Heights  Heights Var Mass Near Small proof c377500c093c: P2 M Ground Theory Heights  Heights Var Mass Near Small proof c377500c093c
-- statement:
--   The P2 M Ground Theory Heights  Heights Var Mass Near Small proof c377500c093c construction uses the P2 M Ground Theory Heights  Heights Var Mass Near Small proof c377500c093c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarMassNearSmall.lean#L74-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarMassNearSmall.lean#L74-L150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarMassNearSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NullSmaller_proof_15fa22cfb07c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_proof_0dafe800e45e

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
open VarMassNearSmall

theorem P2M_GroundTheory_Heights__Heights_VarMassNearSmall_proof_c377500c093c (hCMC : ChartMassCompact.Statement) : VarMassNearSmall.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarMassNearSmall».«proof» := P2M_GroundTheory_Heights__Heights_VarMassNearSmall_proof_c377500c093c
