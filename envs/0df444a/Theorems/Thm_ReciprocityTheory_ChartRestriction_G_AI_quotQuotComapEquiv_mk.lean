-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_quotQuotComapEquiv_mk
-- name    : ReciprocityTheory.ChartRestriction.G.AI.quotQuotComapEquiv_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:24.958191+00:00
-- url     : https://prove2.me/theorems/605c1548-8a7a-44b9-b5fc-1cfed079eb8b
-- title:
--   AI: quot Quot Comap Equiv mk
-- statement:
--   The AI construction uses the quot Quot Comap Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/HeightOneIffDimOne.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/HeightOneIffDimOne.lean#L76-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne
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
universe u v
variable {A : Type u} [CommRing A]

theorem ReciprocityTheory.ChartRestriction.G.AI.quotQuotComapEquiv_mk (a b : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    quotQuotComapEquiv a P (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ b)) =
      Ideal.Quotient.mk _ b := by sorry
