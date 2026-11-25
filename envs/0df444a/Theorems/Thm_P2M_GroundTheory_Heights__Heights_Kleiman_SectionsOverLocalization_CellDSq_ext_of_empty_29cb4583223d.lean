-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_ext_of_empty_29cb4583223d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_ext_of_empty_29cb4583223d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:44.68803+00:00
-- url     : https://prove2.me/theorems/c8019743-9b1b-4fc8-807f-a5898a5c8124
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq ext of empty 29cb4583223d: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq ext of empty
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq ext of empty 29cb4583223d construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq ext of empty 29cb4583223d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L221-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L221-L226

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
variable (S : Type) [CommRing S] [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]
omit [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [LinearOrder K] [Algebra S Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_ext_of_empty_29cb4583223d {m : ℕ} (t : Cell K ι m → Ω) {J : ∀ k, Finset (ι k)} {k : K} (h : J k = ∅) :
    ext m t J = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«ext_of_empty» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_ext_of_empty_29cb4583223d
