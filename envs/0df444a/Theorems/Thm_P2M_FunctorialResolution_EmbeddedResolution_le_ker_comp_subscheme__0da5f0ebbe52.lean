-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_le_ker_comp_subscheme__0da5f0ebbe52
-- name    : P2M_FunctorialResolution_EmbeddedResolution_le_ker_comp_subscheme__0da5f0ebbe52
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:33.609516+00:00
-- url     : https://prove2.me/theorems/7f3762ed-da84-4038-b5a4-2a574f6a55ab
-- title:
--   P2 M Functorial Resolution Embedded Resolution le ker comp subscheme  0da5f0ebbe52: P2 M Functorial Resolution Embedded Resolution le ker comp subscheme  0da5f0ebbe52
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution le ker comp subscheme  0da5f0ebbe52 construction uses the P2 M Functorial Resolution Embedded Resolution le ker comp subscheme  0da5f0ebbe52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothHypersurfaceLocalCoordinates.lean#L82-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothHypersurfaceLocalCoordinates.lean#L82-L90

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

theorem P2M_FunctorialResolution_EmbeddedResolution_le_ker_comp_subscheme__0da5f0ebbe52 (H : P.IdealSheafData) (Z : H.subscheme.IdealSheafData) :
    H ≤ (Z.subschemeι ≫ H.subschemeι).ker := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«le_ker_comp_subschemeι» := P2M_FunctorialResolution_EmbeddedResolution_le_ker_comp_subscheme__0da5f0ebbe52
