-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_locRing_bot_regularN
-- name    : ReciprocityTheory.AnForm.R.locRing_bot_regularN
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:40.033851+00:00
-- url     : https://prove2.me/theorems/c28db9ea-1220-4dad-aa15-3dfc8fec2f34
-- title:
--   R: loc Ring bot regular N
-- statement:
--   The R construction uses the loc Ring bot regular N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjectiveLineMultihomogClassify.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjectiveLineMultihomogClassify.lean#L19-L21

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

theorem ReciprocityTheory.AnForm.R.locRing_bot_regularN {n : ℕ} (p : Fin n → ℂ) :
    IsRegularLocalRing (locRing (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) p) := by sorry
