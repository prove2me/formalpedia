-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ptIdeal_eq_span
-- name    : ReciprocityTheory.AnForm.R.ptIdeal_eq_span
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:37.793802+00:00
-- url     : https://prove2.me/theorems/e5f39d1d-436f-402a-9a2f-224b68064164
-- title:
--   R: pt Ideal eq span
-- statement:
--   The R construction uses the pt Ideal eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjectiveLineMultihomogClassify.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjectiveLineMultihomogClassify.lean#L46-L55

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineMultihomogClassify
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_ptIdeal_eq_span

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

theorem ReciprocityTheory.AnForm.R.ptIdeal_eq_span {n : ℕ} (p : Fin n → ℂ) :
    ptIdeal p = Ideal.span (Set.range fun i => X i - C (p i)) := by sorry
