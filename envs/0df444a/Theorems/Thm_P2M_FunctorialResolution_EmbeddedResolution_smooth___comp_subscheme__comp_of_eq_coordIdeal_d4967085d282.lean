-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_smooth___comp_subscheme__comp_of_eq_coordIdeal_d4967085d282
-- name    : P2M_FunctorialResolution_EmbeddedResolution_smooth___comp_subscheme__comp_of_eq_coordIdeal_d4967085d282
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:44.469181+00:00
-- url     : https://prove2.me/theorems/dae3ec5e-28ca-4a6d-bc33-b2b39cc8da7f
-- title:
--   P2 M Functorial Resolution Embedded Resolution smooth   comp subscheme  comp of eq coord Ideal d4967085d282: P2 M Functorial Resolution Embedded Resolution smooth   comp subscheme  comp of eq coord Id
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution smooth   comp subscheme  comp of eq coord Ideal d4967085d282 construction uses the P2 M Functorial Resolution Embedded Resolution smooth   comp subscheme  comp of eq coord Ideal d4967085d282 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateDivisorSmoothness.lean#L46-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateDivisorSmoothness.lean#L46-L58

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

theorem P2M_FunctorialResolution_EmbeddedResolution_smooth___comp_subscheme__comp_of_eq_coordIdeal_d4967085d282 (Z : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) (c : EtaleChart p U m) (S : Finset (Fin m))
    (h : restrictIdeal Z U = c.coordIdeal S) :
    Smooth ((Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p)) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«smooth_ι_comp_subschemeι_comp_of_eq_coordIdeal» := P2M_FunctorialResolution_EmbeddedResolution_smooth___comp_subscheme__comp_of_eq_coordIdeal_d4967085d282
