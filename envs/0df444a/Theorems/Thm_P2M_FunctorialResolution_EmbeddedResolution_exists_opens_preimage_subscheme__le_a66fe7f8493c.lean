-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_exists_opens_preimage_subscheme__le_a66fe7f8493c
-- name    : P2M_FunctorialResolution_EmbeddedResolution_exists_opens_preimage_subscheme__le_a66fe7f8493c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:40.180544+00:00
-- url     : https://prove2.me/theorems/a6d5078a-f29b-4812-9408-b96ef2e8104c
-- title:
--   P2 M Functorial Resolution Embedded Resolution exists opens preimage subscheme  le a66fe7f8493c: P2 M Functorial Resolution Embedded Resolution exists opens preimage subscheme  le a66fe7f8493c
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution exists opens preimage subscheme  le a66fe7f8493c construction uses the P2 M Functorial Resolution Embedded Resolution exists opens preimage subscheme  le a66fe7f8493c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/IdealSheafOpenRestriction.lean#L281-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/IdealSheafOpenRestriction.lean#L281-L297

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

theorem P2M_FunctorialResolution_EmbeddedResolution_exists_opens_preimage_subscheme__le_a66fe7f8493c {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (x : X)
    (hx : x ∈ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :
    ∃ U : X.Opens, x ∈ U ∧ (Z.subschemeι ⁻¹ᵁ U) ≤ W := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«exists_opens_preimage_subschemeι_le» := P2M_FunctorialResolution_EmbeddedResolution_exists_opens_preimage_subscheme__le_a66fe7f8493c
