-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker_comp_subscheme__ideal_eq_span_coord_17965e032dc1
-- name    : P2M_FunctorialResolution_EmbeddedResolution_ker_comp_subscheme__ideal_eq_span_coord_17965e032dc1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:34.251511+00:00
-- url     : https://prove2.me/theorems/44e361ca-22f4-4940-b723-5841b53fb7fe
-- title:
--   P2 M Functorial Resolution Embedded Resolution ker comp subscheme  ideal eq span coord 17965e032dc1: P2 M Functorial Resolution Embedded Resolution ker comp subscheme  ideal eq span coord 17965e032dc1
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution ker comp subscheme  ideal eq span coord 17965e032dc1 construction uses the P2 M Functorial Resolution Embedded Resolution ker comp subscheme  ideal eq span coord 17965e032dc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothHypersurfaceLocalCoordinates.lean#L94-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothHypersurfaceLocalCoordinates.lean#L94-L132

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
variable {k : Type u} [Field k]

theorem P2M_FunctorialResolution_EmbeddedResolution_ker_comp_subscheme__ideal_eq_span_coord_17965e032dc1 (p : P ⟶ Spec (CommRingCat.of k)) (H : P.IdealSheafData)
    (Z : H.subscheme.IdealSheafData) {U : P.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (c : EtaleChart p U n) (j₀ : Fin n) (S : Finset (Fin n))
    (hH : restrictIdeal H U = c.coordIdeal {j₀})
    (hZ : Z.ideal ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩ =
      Ideal.span
        ((fun j : Fin n =>
          (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord j)) ''
            (S : Set (Fin n)))) :
    (Z.subschemeι ≫ H.subschemeι).ker.ideal ⟨U, hU⟩ =
      Ideal.span (c.coord '' ((insert j₀ S : Finset (Fin n)) : Set (Fin n))) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«ker_comp_subschemeι_ideal_eq_span_coord» := P2M_FunctorialResolution_EmbeddedResolution_ker_comp_subscheme__ideal_eq_span_coord_17965e032dc1
