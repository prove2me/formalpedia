-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_gradMat_swap
-- name    : ReciprocityTheory.AnForm.A.gradMat_swap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:14.592633+00:00
-- url     : https://prove2.me/theorems/2f8fa394-1e72-4848-8c12-b13b79803b9f
-- title:
--   A: grad Mat swap
-- statement:
--   The A construction uses the grad Mat swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L49-L51

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
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.gradMat_swap (v w : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    gradMat w v z = (gradMat v w z)ᴴ := by sorry
