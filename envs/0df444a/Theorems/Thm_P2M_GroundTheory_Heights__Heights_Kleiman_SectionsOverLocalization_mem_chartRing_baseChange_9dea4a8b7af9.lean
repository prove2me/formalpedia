-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mem_chartRing_baseChange_9dea4a8b7af9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mem_chartRing_baseChange_9dea4a8b7af9
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:45.329222+00:00
-- url     : https://prove2.me/theorems/d06236c9-9206-4617-a3a4-565ce64626d2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mem chart Ring base Change 9dea4a8b7af9: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mem chart Ring ba
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mem chart Ring base Change 9dea4a8b7af9 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mem chart Ring base Change 9dea4a8b7af9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeTwist.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeTwist.lean#L29-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
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
open MvPolynomial Kleiman
open scoped Pointwise
noncomputable section
variable {S : Type*} [CommRing S] {O : Type*} [CommRing O] [Algebra S O] {Ω : Type*} [Field Ω]
  [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mem_chartRing_baseChange_9dea4a8b7af9 {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ chartRing O x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«mem_chartRing_baseChange» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mem_chartRing_baseChange_9dea4a8b7af9
