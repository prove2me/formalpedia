-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_renPt_zero
-- name    : ReciprocityTheory.AnForm.R.renPt_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:50:19.977744+00:00
-- url     : https://prove2.me/theorems/9bd02d5a-e934-5db1-8004-f788b6693837
-- title:
--   R: ren Pt zero
-- statement:
--   The R construction uses the ren Pt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/LocTransfer.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/LocTransfer.lean#L71-L78

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
noncomputable section
variable {σ : Type} [Fintype σ]

theorem ReciprocityTheory.AnForm.R.renPt_zero (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) (hz : ∀ h ∈ I, eval z h = 0) :
    ∀ h ∈ I.map (renR σ : MvPolynomial σ ℂ →+* _), eval (renPt z) h = 0 := by sorry
