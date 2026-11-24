-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_comap_subscheme__eq_top_6abe0cb72e4b
-- name    : P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_comap_subscheme__eq_top_6abe0cb72e4b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:37:32.497054+00:00
-- url     : https://prove2.me/theorems/28c218f4-e725-4347-9707-b1f1ad440a09
-- title:
--   P2 M Functorial Resolution Embedded Resolution restrict Ideal comap subscheme  eq top 6abe0cb72e4b: P2 M Functorial Resolution Embedded Resolution restrict Ideal comap subscheme  eq top 6abe0cb72e4b
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution restrict Ideal comap subscheme  eq top 6abe0cb72e4b construction uses the P2 M Functorial Resolution Embedded Resolution restrict Ideal comap subscheme  eq top 6abe0cb72e4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateSubscheme.lean#L604-L610
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateSubscheme.lean#L604-L610

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
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
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

theorem P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_comap_subscheme__eq_top_6abe0cb72e4b {X : Scheme.{u}} (Z : X.IdealSheafData)
    (U : X.Opens) (E : X.IdealSheafData) (hE : restrictIdeal E U = ⊤) :
    restrictIdeal (E.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U) = ⊤ := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«restrictIdeal_comap_subschemeι_eq_top» := P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_comap_subscheme__eq_top_6abe0cb72e4b
