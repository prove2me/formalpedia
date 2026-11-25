-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_ext_ne_zero_a50a237c8230
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_ext_ne_zero_a50a237c8230
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:47.392802+00:00
-- url     : https://prove2.me/theorems/df228d2f-34b5-4663-b067-881bc87f8daf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq ext ne zero a50a237c8230: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq ext ne zero a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq ext ne zero a50a237c8230 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq ext ne zero a50a237c8230 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L167-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L167-L172

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
omit [LinearOrder K] [∀ k, LinearOrder (ι k)] [∀ k, Fintype (ι k)] [Algebra S Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_ext_ne_zero_a50a237c8230 {m : ℕ} (t : Cell K ι m → Ω) (J : ∀ k, Finset (ι k)) (h : ext m t J ≠ 0) :
    ∀ l, (J l).Nonempty := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«ext_ne_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_ext_ne_zero_a50a237c8230
