-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isDiscreteValuationRing_localization_of_height_eq_one_4a287d12d3af
-- name    : P2M_GroundTheory_Heights__Heights_isDiscreteValuationRing_localization_of_height_eq_one_4a287d12d3af
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:41.893094+00:00
-- url     : https://prove2.me/theorems/a3b47784-30da-432a-9022-b87c3a7b196f
-- title:
--   P2 M Ground Theory Heights  Heights is Discrete Valuation Ring localization of height eq one 4a287d12d3af: P2 M Ground Theory Heights  Heights is Discrete Valuation Ring localization of height eq one
-- statement:
--   The P2 M Ground Theory Heights  Heights is Discrete Valuation Ring localization of height eq one 4a287d12d3af construction uses the P2 M Ground Theory Heights  Heights is Discrete Valuation Ring localization of height eq one 4a287d12d3af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalCodimOneUniformiser.lean#L12-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalCodimOneUniformiser.lean#L12-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCodimOneUniformiser
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalCodimOneUniformiser
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial IsLocalRing
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_isDiscreteValuationRing_localization_of_height_eq_one_4a287d12d3af {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (hq : q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isDiscreteValuationRing_localization_of_height_eq_one» := P2M_GroundTheory_Heights__Heights_isDiscreteValuationRing_localization_of_height_eq_one_4a287d12d3af
