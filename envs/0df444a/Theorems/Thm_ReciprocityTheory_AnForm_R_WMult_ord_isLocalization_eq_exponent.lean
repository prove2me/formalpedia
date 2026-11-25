-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_WMult_ord_isLocalization_eq_exponent
-- name    : ReciprocityTheory.AnForm.R.WMult.ord_isLocalization_eq_exponent
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:59:28.883822+00:00
-- url     : https://prove2.me/theorems/b47528ed-b21b-48f6-99ba-a35e80df129a
-- title:
--   WMult: ord is Localization eq exponent
-- statement:
--   The WMult construction uses the ord is Localization eq exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultA.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultA.lean#L59-L70

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.WMult
open AlgebraicGeometry CategoryTheory IsLocalRing
variable {W : Scheme.{0}}

theorem ReciprocityTheory.AnForm.R.WMult.ord_isLocalization_eq_exponent {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ}
    (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) (u : Rˣ) (m : Fin n → ℕ) (i : Fin n) (hi : i ∈ J)
    [(Ideal.span {f i}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S (Ideal.span {f i})] :
    Ring.ord S (algebraMap R S (u * ∏ j ∈ J, f j ^ m j)) = (m i : ℕ∞) := by sorry
