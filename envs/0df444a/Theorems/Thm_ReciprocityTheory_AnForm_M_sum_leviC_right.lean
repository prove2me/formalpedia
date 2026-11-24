-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_sum_leviC_right
-- name    : ReciprocityTheory.AnForm.M.sum_leviC_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:27.706948+00:00
-- url     : https://prove2.me/theorems/d44631b5-5101-4c1f-a66b-cd2cf2203465
-- title:
--   M: sum levi C right
-- statement:
--   The M construction uses the sum levi C right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCIsHermitian.lean#L104-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCIsHermitian.lean#L104-L123

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.M.sum_leviC_right (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (a x : Fin D → ℂ) :
    ∑ j, leviC H a (Pi.single j 1) * x j = leviC H a (star x) := by sorry
