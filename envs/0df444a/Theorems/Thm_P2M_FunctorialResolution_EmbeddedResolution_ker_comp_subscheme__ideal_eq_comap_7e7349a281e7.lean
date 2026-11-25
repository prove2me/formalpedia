-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker_comp_subscheme__ideal_eq_comap_7e7349a281e7
-- name    : P2M_FunctorialResolution_EmbeddedResolution_ker_comp_subscheme__ideal_eq_comap_7e7349a281e7
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:27.028324+00:00
-- url     : https://prove2.me/theorems/c8721752-71bb-4897-8e06-864dbbe8d118
-- title:
--   P2 M Functorial Resolution Embedded Resolution ker comp subscheme  ideal eq comap 7e7349a281e7: P2 M Functorial Resolution Embedded Resolution ker comp subscheme  ideal eq comap 7e7349a281e7
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution ker comp subscheme  ideal eq comap 7e7349a281e7 construction uses the P2 M Functorial Resolution Embedded Resolution ker comp subscheme  ideal eq comap 7e7349a281e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothHypersurfaceLocalCoordinates.lean#L35-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothHypersurfaceLocalCoordinates.lean#L35-L68

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {P : Scheme.{u}}

theorem P2M_FunctorialResolution_EmbeddedResolution_ker_comp_subscheme__ideal_eq_comap_7e7349a281e7 (H : P.IdealSheafData) (Z : H.subscheme.IdealSheafData)
    {U : P.Opens} (hU : IsAffineOpen U) :
    (Z.subschemeι ≫ H.subschemeι).ker.ideal ⟨U, hU⟩ =
      Ideal.comap (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom
        (Z.ideal ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«ker_comp_subschemeι_ideal_eq_comap» := P2M_FunctorialResolution_EmbeddedResolution_ker_comp_subscheme__ideal_eq_comap_7e7349a281e7
