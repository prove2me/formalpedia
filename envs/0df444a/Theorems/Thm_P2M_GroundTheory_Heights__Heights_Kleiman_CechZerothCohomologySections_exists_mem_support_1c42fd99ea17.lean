-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_exists_mem_support_1c42fd99ea17
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_exists_mem_support_1c42fd99ea17
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:11.893102+00:00
-- url     : https://prove2.me/theorems/1f4ac512-715b-4088-afe2-95a44d086191
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections exists mem support 1c42fd99ea17: P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections exists mem supp
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections exists mem support 1c42fd99ea17 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections exists mem support 1c42fd99ea17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsMemSupport.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsMemSupport.lean#L102-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_exists_mem_support_1c42fd99ea17 (hx : x ≠ 0) : ∃ i, i ∈ support x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechZerothCohomologySections».«exists_mem_support» := P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_exists_mem_support_1c42fd99ea17
