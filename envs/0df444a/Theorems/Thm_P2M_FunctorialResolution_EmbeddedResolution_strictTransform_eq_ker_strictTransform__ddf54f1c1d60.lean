-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransform_eq_ker_strictTransform__ddf54f1c1d60
-- name    : P2M_FunctorialResolution_EmbeddedResolution_strictTransform_eq_ker_strictTransform__ddf54f1c1d60
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:00.390698+00:00
-- url     : https://prove2.me/theorems/0097d5df-3fb4-4ed0-acc8-25de55f4eefa
-- title:
--   P2 M Functorial Resolution Embedded Resolution strict Transform eq ker strict Transform  ddf54f1c1d60: P2 M Functorial Resolution Embedded Resolution strict Transform eq ker strict Transform  ddf54f1c
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution strict Transform eq ker strict Transform  ddf54f1c1d60 construction uses the P2 M Functorial Resolution Embedded Resolution strict Transform eq ker strict Transform  ddf54f1c1d60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L43-L45

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

theorem P2M_FunctorialResolution_EmbeddedResolution_strictTransform_eq_ker_strictTransform__ddf54f1c1d60 {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransform π Z D = (strictTransformι π Z D).ker := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«strictTransform_eq_ker_strictTransformι» := P2M_FunctorialResolution_EmbeddedResolution_strictTransform_eq_ker_strictTransform__ddf54f1c1d60
