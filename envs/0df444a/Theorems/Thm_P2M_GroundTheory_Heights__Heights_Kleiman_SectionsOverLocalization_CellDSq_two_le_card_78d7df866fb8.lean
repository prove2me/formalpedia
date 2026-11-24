-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_two_le_card_78d7df866fb8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_two_le_card_78d7df866fb8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:22.52523+00:00
-- url     : https://prove2.me/theorems/9de93b1d-b223-4494-ac0f-925b28dd8cd1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq two le card 78d7df866fb8: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq two le card 78
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq two le card 78d7df866fb8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq two le card 78d7df866fb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L97-L101

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
omit [Fintype K] [LinearOrder K]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_two_le_card_78d7df866fb8 {I : ∀ k, Finset (ι k)} {k : K} {i : ι k} (hi : i ∈ I k)
    (h : ((I k).erase i).Nonempty) : 2 ≤ (I k).card := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«two_le_card» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_two_le_card_78d7df866fb8
