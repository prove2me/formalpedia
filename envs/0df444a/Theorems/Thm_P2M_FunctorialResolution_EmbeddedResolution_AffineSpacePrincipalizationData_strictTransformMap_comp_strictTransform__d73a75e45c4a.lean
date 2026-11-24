-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformMap_comp_strictTransform__d73a75e45c4a
-- name    : P2M_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformMap_comp_strictTransform__d73a75e45c4a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:54:24.383221+00:00
-- url     : https://prove2.me/theorems/3587130b-f58c-4c62-9872-07e30314e62b
-- title:
--   P2 M Functorial Resolution Embedded Resolution Affine Space Principalization Data strict Transform Map comp strict Transform  d73a75e45c4a: P2 M Functorial Resolution Embedded Resolution Affine Space
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution Affine Space Principalization Data strict Transform Map comp strict Transform  d73a75e45c4a construction uses the P2 M Functorial Resolution Embedded Resolution Affine Space Principalization Data strict Transform Map comp strict Transform  d73a75e45c4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedStrictTransform.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedStrictTransform.lean#L96-L98

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

theorem P2M_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformMap_comp_strictTransform__d73a75e45c4a (i : ℕ) :
    S.strictTransformMap i ≫ S.strictTransformι i = S.strictTransformι (i + 1) ≫ S.ambientBlowupMorphism i := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«AffineSpacePrincipalizationData».«strictTransformMap_comp_strictTransformι» := P2M_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformMap_comp_strictTransform__d73a75e45c4a
