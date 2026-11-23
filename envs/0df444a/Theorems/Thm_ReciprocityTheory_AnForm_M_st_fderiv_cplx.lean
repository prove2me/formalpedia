-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_fderiv_cplx
-- name    : ReciprocityTheory.AnForm.M.st_fderiv_cplx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:59.84673+00:00
-- url     : https://prove2.me/theorems/3df7b887-dc21-4cbe-ac61-3c4b9420ecf3
-- title:
--   M: st fderiv cplx
-- statement:
--   The M construction uses the st fderiv cplx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean#L16-L23

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.M.st_fderiv_cplx {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {L : (Fin D → ℂ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f L y) (d : Fin D → ℂ) :
    fderiv ℝ (cplx f) y d = ((L d : ℝ) : ℂ) := by sorry
