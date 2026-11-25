-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ptIdeal_fin_zero
-- name    : ReciprocityTheory.AnForm.R.ptIdeal_fin_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:06.153028+00:00
-- url     : https://prove2.me/theorems/75e95018-ad15-5565-b823-40058f1a65d0
-- title:
--   R: pt Ideal fin zero
-- statement:
--   The R construction uses the pt Ideal fin zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IfaceInh.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IfaceInh.lean#L9-L17

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

theorem ReciprocityTheory.AnForm.R.ptIdeal_fin_zero (p : Fin 0 → ℂ) : ptIdeal p = ⊥ := by sorry
