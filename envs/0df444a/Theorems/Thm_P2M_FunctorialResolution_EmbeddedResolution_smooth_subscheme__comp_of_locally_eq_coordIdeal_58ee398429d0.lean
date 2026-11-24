-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__comp_of_locally_eq_coordIdeal_58ee398429d0
-- name    : P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__comp_of_locally_eq_coordIdeal_58ee398429d0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:55:31.538897+00:00
-- url     : https://prove2.me/theorems/db68ca5f-70d0-4c00-b818-c789467fbad8
-- title:
--   P2 M Functorial Resolution Embedded Resolution smooth subscheme  comp of locally eq coord Ideal 58ee398429d0: P2 M Functorial Resolution Embedded Resolution smooth subscheme  comp of locally eq coord
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution smooth subscheme  comp of locally eq coord Ideal 58ee398429d0 construction uses the P2 M Functorial Resolution Embedded Resolution smooth subscheme  comp of locally eq coord Ideal 58ee398429d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateDivisorSmoothness.lean#L60-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateDivisorSmoothness.lean#L60-L88

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

theorem P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__comp_of_locally_eq_coordIdeal_58ee398429d0 (Z : X.IdealSheafData)
    (h : ∀ x : X, x ∈ Z.support →
      ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n) (S : Finset (Fin n)),
        restrictIdeal Z U = c.coordIdeal S) :
    Smooth (Z.subschemeι ≫ p) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«smooth_subschemeι_comp_of_locally_eq_coordIdeal» := P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__comp_of_locally_eq_coordIdeal_58ee398429d0
