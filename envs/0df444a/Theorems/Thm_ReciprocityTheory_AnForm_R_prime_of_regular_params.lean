-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_prime_of_regular_params
-- name    : ReciprocityTheory.AnForm.R.prime_of_regular_params
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:04.374276+00:00
-- url     : https://prove2.me/theorems/70d86785-2d9d-4500-9243-203dc47df7f7
-- title:
--   R: prime of regular params
-- statement:
--   The R construction uses the prime of regular params property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/Monomial.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/Monomial.lean#L43-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
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

theorem ReciprocityTheory.AnForm.R.prime_of_regular_params [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (i : Fin n) : Prime (f i) := by sorry
