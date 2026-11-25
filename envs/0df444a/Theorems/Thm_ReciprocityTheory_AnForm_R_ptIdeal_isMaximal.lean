-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ptIdeal_isMaximal
-- name    : ReciprocityTheory.AnForm.R.ptIdeal_isMaximal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:51.976054+00:00
-- url     : https://prove2.me/theorems/5c8e0bc9-b25a-5ed3-9b3b-652e23f12351
-- title:
--   R: pt Ideal is Maximal
-- statement:
--   The R construction uses the pt Ideal is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjectiveLineMultihomogClassify.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjectiveLineMultihomogClassify.lean#L16-L17

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

theorem ReciprocityTheory.AnForm.R.ptIdeal_isMaximal {n : ℕ} (p : Fin n → ℂ) : (ptIdeal p).IsMaximal := by sorry
