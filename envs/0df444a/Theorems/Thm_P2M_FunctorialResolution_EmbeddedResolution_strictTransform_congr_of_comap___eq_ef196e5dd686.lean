-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransform_congr_of_comap___eq_ef196e5dd686
-- name    : P2M_FunctorialResolution_EmbeddedResolution_strictTransform_congr_of_comap___eq_ef196e5dd686
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:35.113928+00:00
-- url     : https://prove2.me/theorems/498fc716-46ec-4271-be16-e6f5e9af60e1
-- title:
--   P2 M Functorial Resolution Embedded Resolution strict Transform congr of comap   eq ef196e5dd686: P2 M Functorial Resolution Embedded Resolution strict Transform congr of comap   eq ef196e5dd686
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution strict Transform congr of comap   eq ef196e5dd686 construction uses the P2 M Functorial Resolution Embedded Resolution strict Transform congr of comap   eq ef196e5dd686 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L270-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L270-L275

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

theorem P2M_FunctorialResolution_EmbeddedResolution_strictTransform_congr_of_comap___eq_ef196e5dd686 {X X₁ : Scheme.{u}} (f : X₁ ⟶ X)
    (W D₁ D₂ : X.IdealSheafData)
    (h : D₁.comap (Scheme.Opens.ι W.support.compl) =
      D₂.comap (Scheme.Opens.ι W.support.compl)) :
    Blowup.strictTransform f W D₁ = Blowup.strictTransform f W D₂ := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«strictTransform_congr_of_comap_ι_eq» := P2M_FunctorialResolution_EmbeddedResolution_strictTransform_congr_of_comap___eq_ef196e5dd686
