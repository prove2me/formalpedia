-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isInducing_subscheme__comp___cc236b5b1af5
-- name    : P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isInducing_subscheme__comp___cc236b5b1af5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:49.333424+00:00
-- url     : https://prove2.me/theorems/48eed35f-9451-4a5f-a27a-886e3f05ed20
-- title:
--   P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction is Inducing subscheme  comp   cc236b5b1af5: P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction is Induc
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction is Inducing subscheme  comp   cc236b5b1af5 construction uses the P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction is Inducing subscheme  comp   cc236b5b1af5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean#L114-L124

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

theorem P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isInducing_subscheme__comp___cc236b5b1af5 {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (U : W.Opens) (D : (U.toScheme).IdealSheafData) :
    Topology.IsInducing ⇑(D.subschemeι ≫ U.ι).base := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«OpenImmersionRestriction».«isInducing_subschemeι_comp_ι» := P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isInducing_subscheme__comp___cc236b5b1af5
