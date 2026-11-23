-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv_cplx
-- name    : ReciprocityTheory.AnForm.A.fderiv_cplx
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:31.435802+00:00
-- url     : https://prove2.me/theorems/044165c6-128d-4bec-9aad-310502cbafd5
-- title:
--   A: fderiv cplx
-- statement:
--   The A construction uses the fderiv cplx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L16-L27

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

theorem ReciprocityTheory.AnForm.A.fderiv_cplx (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    fderiv ℝ (cplx v) z = Complex.ofRealCLM.comp (fderiv ℝ v z) := by sorry
