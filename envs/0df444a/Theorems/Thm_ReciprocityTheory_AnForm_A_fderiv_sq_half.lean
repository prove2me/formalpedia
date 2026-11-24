-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv_sq_half
-- name    : ReciprocityTheory.AnForm.A.fderiv_sq_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:00.94306+00:00
-- url     : https://prove2.me/theorems/4ea1e654-72d2-4c18-910e-c2183b44a81d
-- title:
--   A: fderiv sq half
-- statement:
--   The A construction uses the fderiv sq half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L222-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L222-L230

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.A.fderiv_sq_half {D : ℕ} (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hg : DifferentiableAt ℝ g z) :
    fderiv ℝ (fun y => g y ^ 2 / 2) z = g z • fderiv ℝ g z := by sorry
