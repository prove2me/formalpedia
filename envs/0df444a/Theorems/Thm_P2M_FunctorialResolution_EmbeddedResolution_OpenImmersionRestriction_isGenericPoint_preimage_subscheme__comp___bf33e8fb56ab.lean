-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isGenericPoint_preimage_subscheme__comp___bf33e8fb56ab
-- name    : P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isGenericPoint_preimage_subscheme__comp___bf33e8fb56ab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:55.133217+00:00
-- url     : https://prove2.me/theorems/42a89ac3-b842-4659-98fb-1b6ecd274ae5
-- title:
--   P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction is Generic Point preimage subscheme  comp   bf33e8fb56ab: P2 M Functorial Resolution Embedded Resolution Open Immersion Restri
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction is Generic Point preimage subscheme  comp   bf33e8fb56ab construction uses the P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction is Generic Point preimage subscheme  comp   bf33e8fb56ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean#L126-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean#L126-L131

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

theorem P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isGenericPoint_preimage_subscheme__comp___bf33e8fb56ab {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (U : W.Opens) (D : (U.toScheme).IdealSheafData) (T : Set ↥W)
    (ξ : ↥W) (hξ : IsGenericPoint ξ T) (y : ↥(D.subscheme))
    (hy : (D.subschemeι ≫ U.ι).base y = ξ) :
    IsGenericPoint y ((D.subschemeι ≫ U.ι).base ⁻¹' T) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«OpenImmersionRestriction».«isGenericPoint_preimage_subschemeι_comp_ι» := P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isGenericPoint_preimage_subscheme__comp___bf33e8fb56ab
