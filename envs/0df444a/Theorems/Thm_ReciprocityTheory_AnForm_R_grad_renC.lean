-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_grad_renC
-- name    : ReciprocityTheory.AnForm.R.grad_renC
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:08:19.671432+00:00
-- url     : https://prove2.me/theorems/2f8809cb-328c-4e52-a6b7-bd7b9fc61b87
-- title:
--   R: grad ren C
-- statement:
--   The R construction uses the grad ren C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartB.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartB.lean#L27-L36

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
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

theorem ReciprocityTheory.AnForm.R.grad_renC {σ : Type} [Fintype σ] (z : σ → ℂ) (h : MvPolynomial σ ℂ) :
    grad (renPt z) (renC σ h) = fun j => eval z (pderiv ((Fintype.equivFin σ).symm j) h) := by sorry
