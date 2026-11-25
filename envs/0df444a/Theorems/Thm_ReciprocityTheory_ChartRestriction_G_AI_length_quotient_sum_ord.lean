-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_quotient_sum_ord
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_quotient_sum_ord
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:14.774743+00:00
-- url     : https://prove2.me/theorems/e48f03b8-503e-4491-897d-66b9024039fb
-- title:
--   AI: length quotient sum ord
-- statement:
--   The AI construction uses the length quotient sum ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthTwoGeneratorQuotient.lean#L76-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthTwoGeneratorQuotient.lean#L76-L111

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqOfSurjOfKerEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthTwoGeneratorQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
universe u
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

theorem ReciprocityTheory.ChartRestriction.G.AI.length_quotient_sum_ord (h2 : ringKrullDim A = 2) {a : A} (ha : a ≠ 0) (b : A) :
    (∑ᶠ (P : PrimeSpectrum (A ⧸ Ideal.span {a}))
        (_ : ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) = 1),
        length (Localization.AtPrime P.asIdeal)
          (LocalizedModule P.asIdeal.primeCompl (A ⧸ Ideal.span {a})) *
            ordMod P (Ideal.Quotient.mk (Ideal.span {a}) b)) =
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal),
          ordLoc p a * ordMod p b := by sorry
