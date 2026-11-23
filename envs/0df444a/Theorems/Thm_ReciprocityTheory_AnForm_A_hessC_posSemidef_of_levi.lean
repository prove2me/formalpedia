-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_posSemidef_of_levi
-- name    : ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:01.196652+00:00
-- url     : https://prove2.me/theorems/a02b9262-87aa-46d5-a73f-62cdb6a5b54f
-- title:
--   A: hess C pos Semidef of levi
-- statement:
--   The A construction uses the hess C pos Semidef of levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L107-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L107-L121

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
variable {e : ℕ}

theorem ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (h2 : ContDiffAt ℝ 2 φ z)
    (hl : ∀ ξ, 0 ≤ levi φ z ξ) : (hessC φ z).PosSemidef := by sorry
