-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_locRing_bot_dim
-- name    : ReciprocityTheory.AnForm.R.locRing_bot_dim
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:07.157133+00:00
-- url     : https://prove2.me/theorems/5ea929b0-1831-5198-835b-7550ad255a43
-- title:
--   R: loc Ring bot dim
-- statement:
--   The R construction uses the loc Ring bot dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IfaceInh.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IfaceInh.lean#L40-L42

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

theorem ReciprocityTheory.AnForm.R.locRing_bot_dim (p : Fin 0 → ℂ) :
    ringKrullDim (locRing (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p) = 0 := by sorry
