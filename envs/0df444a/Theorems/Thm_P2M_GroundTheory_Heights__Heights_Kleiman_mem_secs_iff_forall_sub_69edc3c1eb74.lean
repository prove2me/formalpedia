-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_iff_forall_sub_69edc3c1eb74
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_iff_forall_sub_69edc3c1eb74
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:28:53.628811+00:00
-- url     : https://prove2.me/theorems/7dc6e1b1-e894-4628-b7a8-befff810d178
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem secs iff forall sub 69edc3c1eb74: P2 M Ground Theory Heights  Heights Kleiman mem secs iff forall sub 69edc3c1eb74
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem secs iff forall sub 69edc3c1eb74 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem secs iff forall sub 69edc3c1eb74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreRestrKer.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreRestrKer.lean#L23-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreRestrKer
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
open MvPolynomial Filter
open scoped Pointwise nonZeroDivisors
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_iff_forall_sub_69edc3c1eb74 {Q : SubSystem S x Ω} {y : Ω} : y ∈ Q.secs ↔ ∀ I, y ∈ Q.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_secs_iff_forall_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_iff_forall_sub_69edc3c1eb74
