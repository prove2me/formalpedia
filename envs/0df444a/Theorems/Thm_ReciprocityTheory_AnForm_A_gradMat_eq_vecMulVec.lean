-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_gradMat_eq_vecMulVec
-- name    : ReciprocityTheory.AnForm.A.gradMat_eq_vecMulVec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:25.209095+00:00
-- url     : https://prove2.me/theorems/7d2c9c8e-5efe-488b-9a41-ae65910f1593
-- title:
--   A: grad Mat eq vec Mul Vec
-- statement:
--   The A construction uses the grad Mat eq vec Mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L44-L47

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

theorem ReciprocityTheory.AnForm.A.gradMat_eq_vecMulVec (v w : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    gradMat v w z = vecMulVec (fun j => dz j (cplx v) z) (star fun k => dz k (cplx w) z) := by sorry
