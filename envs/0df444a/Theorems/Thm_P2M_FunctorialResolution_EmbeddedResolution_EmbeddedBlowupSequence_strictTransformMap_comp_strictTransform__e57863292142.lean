-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformMap_comp_strictTransform__e57863292142
-- name    : P2M_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformMap_comp_strictTransform__e57863292142
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:10.985811+00:00
-- url     : https://prove2.me/theorems/da56c3e2-e9ab-4dae-b39c-19f131d13ed7
-- title:
--   P2 M Functorial Resolution Embedded Resolution Embedded Blowup Sequence strict Transform Map comp strict Transform  e57863292142: P2 M Functorial Resolution Embedded Resolution Embedded Blowup Sequenc
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution Embedded Blowup Sequence strict Transform Map comp strict Transform  e57863292142 construction uses the P2 M Functorial Resolution Embedded Resolution Embedded Blowup Sequence strict Transform Map comp strict Transform  e57863292142 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean#L96-L98

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_EmbeddedResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformMap_comp_strictTransform__d73a75e45c4a

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
open FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
variable (T : EmbeddedBlowupSequence k Y pY)

theorem P2M_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformMap_comp_strictTransform__e57863292142 (i : ℕ) :
    T.strictTransformMap i ≫ T.strictTransformι i = T.strictTransformι (i + 1) ≫ T.blowdown i := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«EmbeddedBlowupSequence».«strictTransformMap_comp_strictTransformι» := P2M_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformMap_comp_strictTransform__e57863292142
