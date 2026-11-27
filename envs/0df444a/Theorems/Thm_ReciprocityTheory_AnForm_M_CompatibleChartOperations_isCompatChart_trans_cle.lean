-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_isCompatChart_trans_cle
-- name    : ReciprocityTheory.AnForm.M.CompatibleChartOperations.isCompatChart_trans_cle
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:02:48.793238+00:00
-- url     : https://prove2.me/theorems/67d8661e-3863-4bc7-a365-9999e8ce43e0
-- title:
--   Compatible Chart Operations: is Compat Chart trans cle
-- statement:
--   The Compatible Chart Operations construction uses the is Compat Chart trans cle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L41-L51

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

theorem ReciprocityTheory.AnForm.M.CompatibleChartOperations.isCompatChart_trans_cle {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    (i : Fin A.n) (L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ)) :
    IsCompatChart A ((A.chart i).trans L.toHomeomorph.toOpenPartialHomeomorph) := by sorry
