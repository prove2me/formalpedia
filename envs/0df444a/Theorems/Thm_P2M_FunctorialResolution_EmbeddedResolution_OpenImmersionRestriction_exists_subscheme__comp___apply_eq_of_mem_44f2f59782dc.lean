-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_exists_subscheme__comp___apply_eq_of_mem_44f2f59782dc
-- name    : P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_exists_subscheme__comp___apply_eq_of_mem_44f2f59782dc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:39.867998+00:00
-- url     : https://prove2.me/theorems/cbef1c92-f011-4e75-b0c4-9bbc5ad9be38
-- title:
--   P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction exists subscheme  comp   apply eq of mem 44f2f59782dc: P2 M Functorial Resolution Embedded Resolution Open Immersion Restricti
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction exists subscheme  comp   apply eq of mem 44f2f59782dc construction uses the P2 M Functorial Resolution Embedded Resolution Open Immersion Restriction exists subscheme  comp   apply eq of mem 44f2f59782dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean#L139-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean#L139-L159

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

theorem P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_exists_subscheme__comp___apply_eq_of_mem_44f2f59782dc {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (U : W.Opens) (D : (U.toScheme).IdealSheafData) (T : Set ↥W)
    (hT : U.ι.base ⁻¹' T ⊆ (D.support : Set ↥(U.toScheme)))
    (x : ↥W) (hxU : x ∈ (U : Set ↥W)) (hxT : x ∈ T) :
    ∃ y : ↥(D.subscheme), (D.subschemeι ≫ U.ι).base y = x := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«OpenImmersionRestriction».«exists_subschemeι_comp_ι_apply_eq_of_mem» := P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_exists_subscheme__comp___apply_eq_of_mem_44f2f59782dc
