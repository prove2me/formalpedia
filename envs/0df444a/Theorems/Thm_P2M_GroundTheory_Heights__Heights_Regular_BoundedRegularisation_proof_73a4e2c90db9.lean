-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_BoundedRegularisation_proof_73a4e2c90db9
-- name    : P2M_GroundTheory_Heights__Heights_Regular_BoundedRegularisation_proof_73a4e2c90db9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:16.097469+00:00
-- url     : https://prove2.me/theorems/c9c32690-3a8e-4667-89af-07f901ed4284
-- title:
--   P2 M Ground Theory Heights  Heights Regular Bounded Regularisation proof 73a4e2c90db9: P2 M Ground Theory Heights  Heights Regular Bounded Regularisation proof 73a4e2c90db9
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Bounded Regularisation proof 73a4e2c90db9 construction uses the P2 M Ground Theory Heights  Heights Regular Bounded Regularisation proof 73a4e2c90db9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsCompactImageClosureMid.lean#L71-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsCompactImageClosureMid.lean#L71-L338

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli shrink regMax tmax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_BoundedRegularisation_proof_73a4e2c90db9 (h0 : BoundedChartComparison.Statement)
    (h1 : BoundedGlue.Statement) (h2 : CutoffsExist.Statement)
    (h3 : ReciprocityTheory.AnForm.A.MollifyStatement) : BoundedRegularisation.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«BoundedRegularisation».«proof» := P2M_GroundTheory_Heights__Heights_Regular_BoundedRegularisation_proof_73a4e2c90db9
