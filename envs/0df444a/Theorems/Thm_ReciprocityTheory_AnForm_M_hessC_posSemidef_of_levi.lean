-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_hessC_posSemidef_of_levi
-- name    : ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:24.556054+00:00
-- url     : https://prove2.me/theorems/0a27434c-700e-472e-82b4-2b08c2044dee
-- title:
--   M: hess C pos Semidef of levi
-- statement:
--   The M construction uses the hess C pos Semidef of levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureA.lean#L29-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureA.lean#L29-L53

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Complex
open scoped ContDiff ComplexOrder Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (hl : ∀ w, 0 ≤ levi f z w) : (hessC f z).PosSemidef := by sorry
