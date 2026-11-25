-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_gs_pderiv_facts
-- name    : ReciprocityTheory.AnForm.R.gs_pderiv_facts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:16.440507+00:00
-- url     : https://prove2.me/theorems/607e2983-cd54-5fde-be77-bf2b25871335
-- title:
--   R: gs pderiv facts
-- statement:
--   The R construction uses the gs pderiv facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/GenSmooth.lean#L48-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/GenSmooth.lean#L48-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
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

theorem ReciprocityTheory.AnForm.R.gs_pderiv_facts {σ : Type*} (p : MvPolynomial σ ℚ) (j : σ) (hj : 0 < degreeOf j p) :
    pderiv j p ≠ 0 ∧ degreeOf j (pderiv j p) < degreeOf j p ∧
      (pderiv j p).vars ⊆ p.vars := by sorry
