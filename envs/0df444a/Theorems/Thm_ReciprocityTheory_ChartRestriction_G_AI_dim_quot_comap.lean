-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_dim_quot_comap
-- name    : ReciprocityTheory.ChartRestriction.G.AI.dim_quot_comap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:56:10.589662+00:00
-- url     : https://prove2.me/theorems/0f20d8f1-352a-4f61-b387-2ce63ec6d4bd
-- title:
--   AI: dim quot comap
-- statement:
--   The AI construction uses the dim quot comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/HeightOneIffDimOne.lean#L136-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/HeightOneIffDimOne.lean#L136-L142

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

theorem ReciprocityTheory.ChartRestriction.G.AI.dim_quot_comap (a : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) =
      ringKrullDim (A ⧸ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal) := by sorry
