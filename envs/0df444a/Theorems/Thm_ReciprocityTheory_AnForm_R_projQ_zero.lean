-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_projQ_zero
-- name    : ReciprocityTheory.AnForm.R.projQ_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:28.4822+00:00
-- url     : https://prove2.me/theorems/297231cf-6702-4f3f-a632-10c950993ab5
-- title:
--   R: proj Q zero
-- statement:
--   The R construction uses the proj Q zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExtCContract.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExtCContract.lean#L36-L38

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

theorem ReciprocityTheory.AnForm.R.projQ_zero (ℓ : ℂ →ₗ[ℚ] ℚ) : projQ ℓ (0 : MvPolynomial σ ℂ) = 0 := by sorry
