-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_comap_comap___49fb03c7437b
-- name    : P2M_FunctorialResolution_EmbeddedResolution_comap_comap___49fb03c7437b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:16.759309+00:00
-- url     : https://prove2.me/theorems/1dbfe250-9e21-4b4b-8247-7c8507b753f8
-- title:
--   P2 M Functorial Resolution Embedded Resolution comap comap   49fb03c7437b: P2 M Functorial Resolution Embedded Resolution comap comap   49fb03c7437b
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution comap comap   49fb03c7437b construction uses the P2 M Functorial Resolution Embedded Resolution comap comap   49fb03c7437b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialSplittingFlatPullback.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialSplittingFlatPullback.lean#L23-L25

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplittingFlatPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X Y : Scheme.{u}}

theorem P2M_FunctorialResolution_EmbeddedResolution_comap_comap___49fb03c7437b (h : Y ⟶ X) (J : X.IdealSheafData) (U : X.Opens) :
    (J.comap h).comap (h ⁻¹ᵁ U).ι = (J.comap U.ι).comap (h ∣_ U) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«comap_comap_ι» := P2M_FunctorialResolution_EmbeddedResolution_comap_comap___49fb03c7437b
