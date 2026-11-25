-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mem_secs_baseChange_6cb983e73d7a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mem_secs_baseChange_6cb983e73d7a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:34.35627+00:00
-- url     : https://prove2.me/theorems/d10547d0-9c26-46c0-b310-f98d133c9b40
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mem secs base Change 6cb983e73d7a: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mem secs base Change 6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mem secs base Change 6cb983e73d7a construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mem secs base Change 6cb983e73d7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L131-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys
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
noncomputable section
variable {S : Type*} [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] {O : Type*} [CommRing O] [Algebra S O]
  [IsLocalization.AtPrime O 𝔪] {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
  {N : ℕ} {x : Fin (N + 1) → Ω}
omit [Algebra S O] [IsScalarTower S O Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mem_secs_baseChange_6cb983e73d7a {G : SubSystem S x Ω} {y : Ω} (hy : y ∈ G.secs) :
    y ∈ (G.baseChange O).secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«mem_secs_baseChange» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mem_secs_baseChange_6cb983e73d7a
