-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_dz_cplx_mul
-- name    : ReciprocityTheory.AnForm.A.dz_cplx_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:58.597887+00:00
-- url     : https://prove2.me/theorems/91cd1d0c-eebb-4b44-a4bc-fb1245df8c1a
-- title:
--   A: dz cplx mul
-- statement:
--   The A construction uses the dz cplx mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L213-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L213-L220

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

theorem ReciprocityTheory.AnForm.A.dz_cplx_mul {D : ℕ} (j : Fin D) (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz j (cplx fun y => f y * g y) z = (f z : ℂ) * dz j (cplx g) z + (g z : ℂ) * dz j (cplx f) z := by sorry
