-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__openSubschemeKer_comp_6059cd915ff9
-- name    : P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__openSubschemeKer_comp_6059cd915ff9
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:13.295291+00:00
-- url     : https://prove2.me/theorems/564664b3-d4da-41fa-85ca-b542cd19b1db
-- title:
--   P2 M Functorial Resolution Embedded Resolution smooth subscheme  open Subscheme Ker comp 6059cd915ff9: P2 M Functorial Resolution Embedded Resolution smooth subscheme  open Subscheme Ker comp 6059cd91
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution smooth subscheme  open Subscheme Ker comp 6059cd915ff9 construction uses the P2 M Functorial Resolution Embedded Resolution smooth subscheme  open Subscheme Ker comp 6059cd915ff9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/IdealSheafOpenRestriction.lean#L64-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/IdealSheafOpenRestriction.lean#L64-L76

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__openSubschemeKer_comp_6059cd915ff9 {X S : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (g : X ⟶ S)
    [Smooth (Z.subschemeι ≫ g)] :
    Smooth ((openSubschemeKer Z W).subschemeι ≫ g) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«smooth_subschemeι_openSubschemeKer_comp» := P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__openSubschemeKer_comp_6059cd915ff9
