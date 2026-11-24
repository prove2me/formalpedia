-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_coeff_projQ
-- name    : ReciprocityTheory.AnForm.R.coeff_projQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:30.264266+00:00
-- url     : https://prove2.me/theorems/bca9c926-e05c-4b6b-b0ac-18d3f88c4e54
-- title:
--   R: coeff proj Q
-- statement:
--   The R construction uses the coeff proj Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExtCContract.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExtCContract.lean#L20-L29

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

theorem ReciprocityTheory.AnForm.R.coeff_projQ (ℓ : ℂ →ₗ[ℚ] ℚ) (q : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    coeff m (projQ ℓ q) = ℓ (coeff m q) := by sorry
