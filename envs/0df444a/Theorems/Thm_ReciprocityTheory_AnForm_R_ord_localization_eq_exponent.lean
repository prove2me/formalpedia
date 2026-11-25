-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ord_localization_eq_exponent
-- name    : ReciprocityTheory.AnForm.R.ord_localization_eq_exponent
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:18.044472+00:00
-- url     : https://prove2.me/theorems/44d7175b-f7f3-4385-b156-eb5650c98f70
-- title:
--   R: ord localization eq exponent
-- statement:
--   The R construction uses the ord localization eq exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/Monomial.lean#L76-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/Monomial.lean#L76-L122

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

theorem ReciprocityTheory.AnForm.R.ord_localization_eq_exponent [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) (u : Rˣ) (m : Fin n → ℕ) (i : Fin n) (hi : i ∈ J)
    [(Ideal.span {f i}).IsPrime] :
    Ring.ord (Localization.AtPrime (Ideal.span {f i}))
        (algebraMap R (Localization.AtPrime (Ideal.span {f i})) (u * ∏ j ∈ J, f j ^ m j)) =
      (m i : ℕ∞) := by sorry
