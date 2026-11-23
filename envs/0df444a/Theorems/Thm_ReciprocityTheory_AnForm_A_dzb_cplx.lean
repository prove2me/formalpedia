-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_dzb_cplx
-- name    : ReciprocityTheory.AnForm.A.dzb_cplx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:17.181054+00:00
-- url     : https://prove2.me/theorems/2f5695a3-52f9-4038-a914-3c4bbc1d21b2
-- title:
--   A: dzb cplx
-- statement:
--   The A construction uses the dzb cplx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L34-L37

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

theorem ReciprocityTheory.AnForm.A.dzb_cplx (j : Fin D) (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    dzb j (cplx v) z = ((fderiv ℝ v z (Pi.single j 1) : ℂ) +
      Complex.I * (fderiv ℝ v z (Complex.I • Pi.single j 1) : ℂ)) / 2 := by sorry
