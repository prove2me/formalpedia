-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker_comap___eq_ker_of_isIso_comp_7508c0c594b4
-- name    : P2M_FunctorialResolution_EmbeddedResolution_ker_comap___eq_ker_of_isIso_comp_7508c0c594b4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:18.687234+00:00
-- url     : https://prove2.me/theorems/2996459b-744d-4592-8d32-92ad38b22681
-- title:
--   P2 M Functorial Resolution Embedded Resolution ker comap   eq ker of is Iso comp 7508c0c594b4: P2 M Functorial Resolution Embedded Resolution ker comap   eq ker of is Iso comp 7508c0c594b4
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution ker comap   eq ker of is Iso comp 7508c0c594b4 construction uses the P2 M Functorial Resolution Embedded Resolution ker comap   eq ker of is Iso comp 7508c0c594b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L130-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L130-L134

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ReducedSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
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

theorem P2M_FunctorialResolution_EmbeddedResolution_ker_comap___eq_ker_of_isIso_comp_7508c0c594b4 {W T S : Scheme.{u}} (m : W ⟶ T) [QuasiCompact m]
    (V : T.Opens) (n : S ⟶ V.toScheme) (e : S ⟶ (m ⁻¹ᵁ V).toScheme) [IsIso e]
    (h : e ≫ (m ∣_ V) = n) :
    (Scheme.Hom.ker m).comap (Scheme.Opens.ι V) = Scheme.Hom.ker n := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«ker_comap_ι_eq_ker_of_isIso_comp» := P2M_FunctorialResolution_EmbeddedResolution_ker_comap___eq_ker_of_isIso_comp_7508c0c594b4
