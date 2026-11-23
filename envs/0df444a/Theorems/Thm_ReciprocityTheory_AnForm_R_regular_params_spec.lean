-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_regular_params_spec
-- name    : ReciprocityTheory.AnForm.R.regular_params_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:11.439797+00:00
-- url     : https://prove2.me/theorems/52a1ede5-7ebe-4d93-a76f-f8243d36cf6d
-- title:
--   R: regular params spec
-- statement:
--   The R construction uses the regular params spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/RegDom.lean#L169-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/RegDom.lean#L169-L224

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

theorem ReciprocityTheory.AnForm.R.regular_params_spec [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R) :
    (∀ i, f i ∉ maximalIdeal R ^ 2) ∧ ∀ i j, i ≠ j → ¬ Associated (f i) (f j) := by sorry
