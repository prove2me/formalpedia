-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_sub_C_eval_mem_span
-- name    : ReciprocityTheory.AnForm.R.sub_C_eval_mem_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:16.066883+00:00
-- url     : https://prove2.me/theorems/da6a14c6-d865-5a90-863d-7e1241e0833c
-- title:
--   R: sub C eval mem span
-- statement:
--   The R construction uses the sub C eval mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjectiveLineMultihomogClassify.lean#L31-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjectiveLineMultihomogClassify.lean#L31-L44

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

theorem ReciprocityTheory.AnForm.R.sub_C_eval_mem_span {n : ℕ} (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    f - C (eval p f) ∈ Ideal.span (Set.range fun i => X i - C (p i)) := by sorry
