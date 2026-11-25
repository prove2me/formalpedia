-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_cellD_apply_not_14cc3ff14943
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_cellD_apply_not_14cc3ff14943
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:38.455341+00:00
-- url     : https://prove2.me/theorems/b48d288a-7663-553c-9ca5-6983838341ee
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq cell D apply not 14cc3ff14943: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq cell D ap
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq cell D apply not 14cc3ff14943 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq cell D apply not 14cc3ff14943 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L187-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L187-L189

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
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_cellD_apply_not_14cc3ff14943 (y : (Σ k, ι k) → Ω) (m : ℕ) (t : Cell K ι m → Ω) (J : Cell K ι (m + 1))
    (hJ : ¬ CellMeets y J.1) : cellD S y m t J = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«cellD_apply_not» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_cellD_apply_not_14cc3ff14943
