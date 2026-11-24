-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_orderAt_comap___3b37585930bd
-- name    : P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_orderAt_comap___3b37585930bd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:59.578557+00:00
-- url     : https://prove2.me/theorems/ad5b83c9-9670-4e9c-a7be-cb0fc12499fe
-- title:
--   P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction order At comap   3b37585930bd: P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction order At comap   3b37
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction order At comap   3b37585930bd construction uses the P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction order At comap   3b37585930bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealAssignment.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealAssignment.lean#L62-L65

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

theorem P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_orderAt_comap___3b37585930bd (W : Scheme.{u}) (V : W.Opens) (I : W.IdealSheafData)
    (y : ↥(V.toScheme)) :
    orderAt (I.comap V.ι) y = orderAt I (V.ι.base y) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«OpenImmersionRestriction».«orderAt_comap_ι» := P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_orderAt_comap___3b37585930bd
