-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_agreeNear_comap___bbe540cce3bf
-- name    : P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_agreeNear_comap___bbe540cce3bf
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:47.951074+00:00
-- url     : https://prove2.me/theorems/89b44338-5f14-4d57-aa24-a499c838fe7e
-- title:
--   P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction agree Near comap   bbe540cce3bf: P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction agree Near comap
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction agree Near comap   bbe540cce3bf construction uses the P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction agree Near comap   bbe540cce3bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealAssignment.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealAssignment.lean#L53-L60

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealAssignment
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

theorem P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_agreeNear_comap___bbe540cce3bf (W : Scheme.{u}) (V : W.Opens) (I J : W.IdealSheafData)
    (y : ↥(V.toScheme)) (h : AgreeNear I J (V.ι.base y)) :
    AgreeNear (I.comap V.ι) (J.comap V.ι) y := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«OpenImmersionRestriction».«agreeNear_comap_ι» := P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_agreeNear_comap___bbe540cce3bf
