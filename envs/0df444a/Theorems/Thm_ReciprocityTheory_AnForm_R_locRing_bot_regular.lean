-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_locRing_bot_regular
-- name    : ReciprocityTheory.AnForm.R.locRing_bot_regular
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:56.068983+00:00
-- url     : https://prove2.me/theorems/9ea77290-9f3d-4bd0-8d96-755cf6d7c352
-- title:
--   R: loc Ring bot regular
-- statement:
--   The R construction uses the loc Ring bot regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IfaceInh.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IfaceInh.lean#L37-L38

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IfaceInh
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

theorem ReciprocityTheory.AnForm.R.locRing_bot_regular (p : Fin 0 → ℂ) :
    IsRegularLocalRing (locRing (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p) := by sorry
