-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_prod_option_eq_prod_zpow
-- name    : ReciprocityTheory.AnForm.M.prod_option_eq_prod_zpow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:33:14.899397+00:00
-- url     : https://prove2.me/theorems/754d1283-89ff-4585-a2b9-a8ed6f539839
-- title:
--   M: prod option eq prod zpow
-- statement:
--   The M construction uses the prod option eq prod zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LogInt.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LogInt.lean#L37-L43

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.AnForm.M.prod_option_eq_prod_zpow {e r : ℕ} (σ : Fin r → Option (Fin e)) (m : Fin r → ℕ)
    (w : Fin e → ℂ) (g : Fin r → ℂ) (hg : ∀ k, g k = ∏ i, if σ k = some i then w i ^ m k else 1) :
    ∏ k, g k = ∏ i, w i ^ (((∑ k ∈ Finset.univ.filter (fun k => σ k = some i), m k : ℕ)) : ℤ) := by sorry
