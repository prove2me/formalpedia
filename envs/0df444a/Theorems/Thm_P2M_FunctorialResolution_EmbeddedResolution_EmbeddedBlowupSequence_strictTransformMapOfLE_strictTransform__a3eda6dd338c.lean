-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformMapOfLE_strictTransform__a3eda6dd338c
-- name    : P2M_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformMapOfLE_strictTransform__a3eda6dd338c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:28.757867+00:00
-- url     : https://prove2.me/theorems/68dd0c77-c52b-4923-ab75-98b1594663ee
-- title:
--   P2 M Functorial Resolution Embedded Resolution Embedded Blowup Sequence strict Transform Map Of LE strict Transform  a3eda6dd338c: P2 M Functorial Resolution Embedded Resolution Embedded Blowup Sequen
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution Embedded Blowup Sequence strict Transform Map Of LE strict Transform  a3eda6dd338c construction uses the P2 M Functorial Resolution Embedded Resolution Embedded Blowup Sequence strict Transform Map Of LE strict Transform  a3eda6dd338c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrictTransformTower.lean#L53-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrictTransformTower.lean#L53-L72

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrictTransformTower
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
variable (S : EmbeddedBlowupSequence k Y pY)

theorem P2M_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformMapOfLE_strictTransform__a3eda6dd338c {a b : ℕ} (h : a ≤ b) :
    S.strictTransformMapOfLE h ≫ S.strictTransformι a = S.strictTransformι b ≫ S.ambientSeq.transitionMap h := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«EmbeddedBlowupSequence».«strictTransformMapOfLE_strictTransformι» := P2M_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformMapOfLE_strictTransform__a3eda6dd338c
