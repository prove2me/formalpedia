-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_prod_prod_update
-- name    : ReciprocityTheory.AnForm.R.prod_prod_update
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:30.147735+00:00
-- url     : https://prove2.me/theorems/9095caeb-a0c1-5cb5-b0f8-c24b531e4010
-- title:
--   R: prod prod update
-- statement:
--   The R construction uses the prod prod update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L41-L51

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
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
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.prod_prod_update {M : Type*} [CommMonoid M] [DecidableEq K] (x : (Σ k, ι k) → M)
    (p p' : (k : K) → ι k) :
    (∏ k, ∏ j, x ⟨j, Function.update p k (p' k) j⟩) * ∏ j, x ⟨j, p j⟩ =
      (∏ k, x ⟨k, p' k⟩) * (∏ j, x ⟨j, p j⟩) ^ Fintype.card K := by sorry
