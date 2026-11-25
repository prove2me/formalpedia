-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_offset_update_2ba4b02ed54e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_offset_update_2ba4b02ed54e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:51.722087+00:00
-- url     : https://prove2.me/theorems/1c3c8d34-63cb-407a-be20-815cf3da2f59
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq offset update 2ba4b02ed54e: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq offset updat
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq offset update 2ba4b02ed54e construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq offset update 2ba4b02ed54e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L44-L48

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
omit [∀ k, LinearOrder (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_offset_update_2ba4b02ed54e (I : ∀ k, Finset (ι k)) (k : K) (X : Finset (ι k)) :
    ∑ l ∈ Finset.univ.filter (· < k), ((Function.update I k X l).card - 1) =
      ∑ l ∈ Finset.univ.filter (· < k), ((I l).card - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«offset_update» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_offset_update_2ba4b02ed54e
