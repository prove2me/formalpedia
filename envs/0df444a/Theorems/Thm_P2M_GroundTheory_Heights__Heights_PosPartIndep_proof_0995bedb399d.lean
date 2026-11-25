-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PosPartIndep_proof_0995bedb399d
-- name    : P2M_GroundTheory_Heights__Heights_PosPartIndep_proof_0995bedb399d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:48.444794+00:00
-- url     : https://prove2.me/theorems/41d50dd9-c819-5600-a5d8-4ab3968c04b7
-- title:
--   P2 M Ground Theory Heights  Heights Pos Part Indep proof 0995bedb399d: P2 M Ground Theory Heights  Heights Pos Part Indep proof 0995bedb399d
-- statement:
--   The P2 M Ground Theory Heights  Heights Pos Part Indep proof 0995bedb399d construction uses the P2 M Ground Theory Heights  Heights Pos Part Indep proof 0995bedb399d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPosPartIndependent.lean#L16-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPosPartIndependent.lean#L16-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_proof_4b5bf5e5d261
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1

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
open MvPolynomial MeasureTheory ComplexSets Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_PosPartIndep_proof_0995bedb399d (h : SheetOnlyNull.Statement) (hL : PosPartLocal.Statement)
    (hS : PosPartSplit.Statement) : PosPartIndep.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PosPartIndep».«proof» := P2M_GroundTheory_Heights__Heights_PosPartIndep_proof_0995bedb399d
