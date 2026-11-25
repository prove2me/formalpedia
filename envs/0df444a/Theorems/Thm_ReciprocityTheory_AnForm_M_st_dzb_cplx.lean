-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_dzb_cplx
-- name    : ReciprocityTheory.AnForm.M.st_dzb_cplx
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:04:40.097804+00:00
-- url     : https://prove2.me/theorems/a481123a-c9fd-4057-b5ff-de38220b46c9
-- title:
--   M: st dzb cplx
-- statement:
--   The M construction uses the st dzb cplx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean#L31-L35

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

theorem ReciprocityTheory.AnForm.M.st_dzb_cplx {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {L : (Fin D → ℂ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f L y) (j : Fin D) :
    dzb j (cplx f) y = (((L (Pi.single j 1) : ℝ) : ℂ) +
      Complex.I * ((L (Complex.I • Pi.single j 1) : ℝ) : ℂ)) / 2 := by sorry
