-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_projQ_add
-- name    : ReciprocityTheory.AnForm.R.projQ_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:48.468577+00:00
-- url     : https://prove2.me/theorems/5fa4d1de-5d9d-5cf2-b801-4937909d8da5
-- title:
--   R: proj Q add
-- statement:
--   The R construction uses the proj Q add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExtCContract.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExtCContract.lean#L31-L34

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExtCContract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
variable {σ : Type} [Fintype σ]

theorem ReciprocityTheory.AnForm.R.projQ_add (ℓ : ℂ →ₗ[ℚ] ℚ) (a b : MvPolynomial σ ℂ) :
    projQ ℓ (a + b) = projQ ℓ a + projQ ℓ b := by sorry
