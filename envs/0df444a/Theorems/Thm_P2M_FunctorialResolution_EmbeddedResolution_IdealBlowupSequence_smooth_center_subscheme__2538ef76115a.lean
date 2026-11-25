-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_IdealBlowupSequence_smooth_center_subscheme__2538ef76115a
-- name    : P2M_FunctorialResolution_EmbeddedResolution_IdealBlowupSequence_smooth_center_subscheme__2538ef76115a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:20.280075+00:00
-- url     : https://prove2.me/theorems/a17d5788-aa86-4635-b75a-eb89f3bd7ca5
-- title:
--   P2 M Functorial Resolution Embedded Resolution Ideal Blowup Sequence smooth center subscheme  2538ef76115a: P2 M Functorial Resolution Embedded Resolution Ideal Blowup Sequence smooth center subscheme
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution Ideal Blowup Sequence smooth center subscheme  2538ef76115a construction uses the P2 M Functorial Resolution Embedded Resolution Ideal Blowup Sequence smooth center subscheme  2538ef76115a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean#L83-L85

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IdealBlowupSequence
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}

theorem P2M_FunctorialResolution_EmbeddedResolution_IdealBlowupSequence_smooth_center_subscheme__2538ef76115a (s : IdealBlowupSequence p I E) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    AlgebraicGeometry.Smooth ((s.toSequenceOfBlowups.center i).subschemeι ≫ s.structureMorphism i) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«IdealBlowupSequence».«smooth_center_subschemeι» := P2M_FunctorialResolution_EmbeddedResolution_IdealBlowupSequence_smooth_center_subscheme__2538ef76115a
