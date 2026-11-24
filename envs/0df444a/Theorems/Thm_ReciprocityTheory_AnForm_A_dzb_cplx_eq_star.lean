-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_dzb_cplx_eq_star
-- name    : ReciprocityTheory.AnForm.A.dzb_cplx_eq_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:00.93145+00:00
-- url     : https://prove2.me/theorems/1bc0294d-8414-40c7-b347-3bd3568a66be
-- title:
--   A: dzb cplx eq star
-- statement:
--   The A construction uses the dzb cplx eq star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L39-L42

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

theorem ReciprocityTheory.AnForm.A.dzb_cplx_eq_star (j : Fin D) (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    dzb j (cplx v) z = star (dz j (cplx v) z) := by sorry
