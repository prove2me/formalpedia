-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_prod_reindex_option
-- name    : ReciprocityTheory.AnForm.R.prod_reindex_option
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:35.994988+00:00
-- url     : https://prove2.me/theorems/2e80ced3-e86e-45ab-8d36-ef2d695abeba
-- title:
--   R: prod reindex option
-- statement:
--   The R construction uses the prod reindex option property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean#L73-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean#L73-L110

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

theorem ReciprocityTheory.AnForm.R.prod_reindex_option {e rc : ℕ} (J : Finset (Fin e)) (σ : Fin e → Option (Fin rc))
    (hnone : ∀ l, σ l = none ↔ l ∉ J) (σ' : Fin rc → Option (Fin e))
    (hσ' : ∀ k l, σ' k = some l ↔ σ l = some k) (m : Fin rc → ℕ) (w : Fin e → ℂ) :
    ∏ l ∈ J, w l ^ (σ l).elim 0 m = ∏ k, Option.elim (σ' k) 1 (fun i => w i ^ m k) := by sorry
