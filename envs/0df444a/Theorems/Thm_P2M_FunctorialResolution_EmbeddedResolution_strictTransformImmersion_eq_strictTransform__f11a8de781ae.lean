-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransformImmersion_eq_strictTransform__f11a8de781ae
-- name    : P2M_FunctorialResolution_EmbeddedResolution_strictTransformImmersion_eq_strictTransform__f11a8de781ae
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:15.066415+00:00
-- url     : https://prove2.me/theorems/c87930e6-f4a2-4718-9673-fd2ad5b9023b
-- title:
--   P2 M Functorial Resolution Embedded Resolution strict Transform Immersion eq strict Transform  f11a8de781ae: P2 M Functorial Resolution Embedded Resolution strict Transform Immersion eq strict Transfo
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution strict Transform Immersion eq strict Transform  f11a8de781ae construction uses the P2 M Functorial Resolution Embedded Resolution strict Transform Immersion eq strict Transform  f11a8de781ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L39-L41

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

theorem P2M_FunctorialResolution_EmbeddedResolution_strictTransformImmersion_eq_strictTransform__f11a8de781ae {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransformImmersion π Z D = strictTransformι π Z D := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«strictTransformImmersion_eq_strictTransformι» := P2M_FunctorialResolution_EmbeddedResolution_strictTransformImmersion_eq_strictTransform__f11a8de781ae
