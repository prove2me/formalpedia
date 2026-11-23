-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_dz_cplx
-- name    : ReciprocityTheory.AnForm.A.dz_cplx
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:41.053824+00:00
-- url     : https://prove2.me/theorems/4f177c2a-12ed-4bbe-bce8-97844927d76f
-- title:
--   A: dz cplx
-- statement:
--   The A construction uses the dz cplx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L29-L32

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

theorem ReciprocityTheory.AnForm.A.dz_cplx (j : Fin D) (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    dz j (cplx v) z = ((fderiv ℝ v z (Pi.single j 1) : ℂ) -
      Complex.I * (fderiv ℝ v z (Complex.I • Pi.single j 1) : ℂ)) / 2 := by sorry
