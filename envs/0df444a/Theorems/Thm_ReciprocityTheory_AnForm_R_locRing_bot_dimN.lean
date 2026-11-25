-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_locRing_bot_dimN
-- name    : ReciprocityTheory.AnForm.R.locRing_bot_dimN
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:37.599868+00:00
-- url     : https://prove2.me/theorems/90def648-a2e8-54bd-ac1d-040f32d13b47
-- title:
--   R: loc Ring bot dim N
-- statement:
--   The R construction uses the loc Ring bot dim N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjectiveLineMultihomogClassify.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjectiveLineMultihomogClassify.lean#L23-L29

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineMultihomogClassify
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial OnePoint Filter Topology
noncomputable section

theorem ReciprocityTheory.AnForm.R.locRing_bot_dimN {n : ℕ} (p : Fin n → ℂ) :
    ringKrullDim (locRing (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) p) = n := by sorry
