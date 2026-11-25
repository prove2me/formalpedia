-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_prime_of_not_mem_sq
-- name    : ReciprocityTheory.AnForm.R.prime_of_not_mem_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:17.246169+00:00
-- url     : https://prove2.me/theorems/a4ccffc3-8c91-5eb0-b70f-9a90d0849a59
-- title:
--   R: prime of not mem sq
-- statement:
--   The R construction uses the prime of not mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/RegDom.lean#L157-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/RegDom.lean#L157-L167

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

theorem ReciprocityTheory.AnForm.R.prime_of_not_mem_sq [IsRegularLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) : Prime x := by sorry
