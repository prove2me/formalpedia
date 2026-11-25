-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_WeightedDegree_charZero_fractionRing_351d615b3fd8
-- name    : P2M_GroundTheory_Heights__Heights_WeightedDegree_charZero_fractionRing_351d615b3fd8
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:44:23.068084+00:00
-- url     : https://prove2.me/theorems/d0ed2842-5bb4-4d01-b6d2-8894350bae2a
-- title:
--   P2 M Ground Theory Heights  Heights Weighted Degree char Zero fraction Ring 351d615b3fd8: P2 M Ground Theory Heights  Heights Weighted Degree char Zero fraction Ring 351d615b3fd8
-- statement:
--   The P2 M Ground Theory Heights  Heights Weighted Degree char Zero fraction Ring 351d615b3fd8 construction uses the P2 M Ground Theory Heights  Heights Weighted Degree char Zero fraction Ring 351d615b3fd8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightedHomogeneousComponentMap.lean#L167-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightedHomogeneousComponentMap.lean#L167-L172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConservationOfNumberLE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightedHomogeneousComponentMap
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
open MvPolynomial NumbersDVR
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.WeightedDegree

theorem P2M_GroundTheory_Heights__Heights_WeightedDegree_charZero_fractionRing_351d615b3fd8 (O : Type) [CommRing O] [IsDomain O]
    (h : Function.Injective (Int.castRingHom O)) : CharZero (FractionRing O) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«WeightedDegree».«charZero_fractionRing» := P2M_GroundTheory_Heights__Heights_WeightedDegree_charZero_fractionRing_351d615b3fd8
