-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_isCompatChart_restrOpen
-- name    : ReciprocityTheory.AnForm.M.CompatibleChartOperations.isCompatChart_restrOpen
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:03:05.577989+00:00
-- url     : https://prove2.me/theorems/9fd37930-825b-4cd7-8e1f-6a23ecfd47b4
-- title:
--   Compatible Chart Operations: is Compat Chart restr Open
-- statement:
--   The Compatible Chart Operations construction uses the is Compat Chart restr Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L53-L58

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
open ReciprocityTheory.AnForm.M.CompatibleChartOperations

theorem ReciprocityTheory.AnForm.M.CompatibleChartOperations.isCompatChart_restrOpen {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    (i : Fin A.n) (s : Set X) (hs : IsOpen s) : IsCompatChart A ((A.chart i).restrOpen s hs) := by sorry
