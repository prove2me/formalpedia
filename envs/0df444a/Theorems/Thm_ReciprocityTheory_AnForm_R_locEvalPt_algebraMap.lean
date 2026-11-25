-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_locEvalPt_algebraMap
-- name    : ReciprocityTheory.AnForm.R.locEvalPt_algebraMap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:23.572088+00:00
-- url     : https://prove2.me/theorems/f8cbfac5-6ca0-5c10-bd92-b7c141a19d0f
-- title:
--   R: loc Eval Pt algebra Map
-- statement:
--   The R construction uses the loc Eval Pt algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean#L38-L41

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.R.locEvalPt_algebraMap (I : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ g ∈ I, eval p g = 0) (g : MvPolynomial (Fin n) ℂ) :
    locEvalPt I p hp (Ideal.Quotient.mk _ (algebraMap _ (locPt p) g)) = eval p g := by sorry
