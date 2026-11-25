-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_meets_rem_3cd5209d76fc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_meets_rem_3cd5209d76fc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:25.137802+00:00
-- url     : https://prove2.me/theorems/750ac962-bbd1-4039-8acb-b75fedd7f911
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq meets rem 3cd5209d76fc: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq meets rem 3cd520
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq meets rem 3cd5209d76fc construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq meets rem 3cd5209d76fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L193-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L193-L202

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
omit [∀ k, Fintype (ι k)] [Fintype K] [Algebra S Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_meets_rem_3cd5209d76fc {y : (Σ k, ι k) → Ω} {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) (p : Σ k, ι k) :
    CellMeets y (rem I p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«meets_rem» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_meets_rem_3cd5209d76fc
