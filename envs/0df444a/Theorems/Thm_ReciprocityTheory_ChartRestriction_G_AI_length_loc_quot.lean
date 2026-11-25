-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_loc_quot
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_loc_quot
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:29.436792+00:00
-- url     : https://prove2.me/theorems/ced15d03-e390-5914-9cfe-e04afef1ca96
-- title:
--   AI: length loc quot
-- statement:
--   The AI construction uses the length loc quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/HeightOneIffDimOne.lean#L144-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/HeightOneIffDimOne.lean#L144-L173

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
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

theorem ReciprocityTheory.ChartRestriction.G.AI.length_loc_quot (a : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    length (Localization.AtPrime P.asIdeal)
        (LocalizedModule P.asIdeal.primeCompl (A ⧸ Ideal.span {a})) =
      ordLoc (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P) a := by sorry
