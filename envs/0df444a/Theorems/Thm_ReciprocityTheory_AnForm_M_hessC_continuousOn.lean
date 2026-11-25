-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_hessC_continuousOn
-- name    : ReciprocityTheory.AnForm.M.hessC_continuousOn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:18.013674+00:00
-- url     : https://prove2.me/theorems/602d1327-2a1a-4df3-8e3b-b912f2cb5dc8
-- title:
--   M: hess C continuous On
-- statement:
--   The M construction uses the hess C continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LocDens.lean#L65-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LocDens.lean#L65-L82

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff ComplexOrder Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.M.hessC_continuousOn {D : ℕ} (ψ : (Fin D → ℂ) → ℝ) (V : Set (Fin D → ℂ)) (hV : IsOpen V)
    (hψ : ContDiffOn ℝ 2 ψ V) : ContinuousOn (hessC ψ) V := by sorry
