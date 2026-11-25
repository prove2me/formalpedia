-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isRegularLocalRing_quotient_of_not_mem_sq
-- name    : ReciprocityTheory.AnForm.R.isRegularLocalRing_quotient_of_not_mem_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:13.798356+00:00
-- url     : https://prove2.me/theorems/f2aecdf7-3a95-5919-8bf3-3f9b0ce7e2af
-- title:
--   R: is Regular Local Ring quotient of not mem sq
-- statement:
--   The R construction uses the is Regular Local Ring quotient of not mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/RegDom.lean#L13-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/RegDom.lean#L13-L155

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open IsLocalRing
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.AnForm.R.isRegularLocalRing_quotient_of_not_mem_sq [IsRegularLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by sorry
