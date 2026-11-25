-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__comp_of_hasStrictNormalCrossingsWith_224aeeb9bb66
-- name    : P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__comp_of_hasStrictNormalCrossingsWith_224aeeb9bb66
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:54:53.12375+00:00
-- url     : https://prove2.me/theorems/3b2bfd36-782c-4eb9-b09e-d40516be2c34
-- title:
--   P2 M Functorial Resolution Embedded Resolution smooth subscheme  comp of has Strict Normal Crossings With 224aeeb9bb66: P2 M Functorial Resolution Embedded Resolution smooth subscheme  comp of has Str
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution smooth subscheme  comp of has Strict Normal Crossings With 224aeeb9bb66 construction uses the P2 M Functorial Resolution Embedded Resolution smooth subscheme  comp of has Strict Normal Crossings With 224aeeb9bb66 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateDivisorSmoothness.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateDivisorSmoothness.lean#L90-L96

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_AffineSpaceSmooth
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
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
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}

theorem P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__comp_of_hasStrictNormalCrossingsWith_224aeeb9bb66 (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (h : HasStrictNormalCrossingsWith p Z E) : Smooth (Z.subschemeι ≫ p) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith» := P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__comp_of_hasStrictNormalCrossingsWith_224aeeb9bb66
