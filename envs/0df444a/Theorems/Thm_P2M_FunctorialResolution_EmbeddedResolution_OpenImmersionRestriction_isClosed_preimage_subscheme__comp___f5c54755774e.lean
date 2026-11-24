-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isClosed_preimage_subscheme__comp___f5c54755774e
-- name    : P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isClosed_preimage_subscheme__comp___f5c54755774e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:33.350834+00:00
-- url     : https://prove2.me/theorems/2c78a987-4ba3-4460-8bac-419b7305f3dd
-- title:
--   P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction is Closed preimage subscheme  comp   f5c54755774e: P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction i
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction is Closed preimage subscheme  comp   f5c54755774e construction uses the P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction is Closed preimage subscheme  comp   f5c54755774e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean#L133-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean#L133-L137

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
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

theorem P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isClosed_preimage_subscheme__comp___f5c54755774e {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (U : W.Opens) (D : (U.toScheme).IdealSheafData) (T : Set ↥W)
    (hT : IsClosed T) :
    IsClosed ((D.subschemeι ≫ U.ι).base ⁻¹' T) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«OpenImmersionRestriction».«isClosed_preimage_subschemeι_comp_ι» := P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isClosed_preimage_subscheme__comp___f5c54755774e
