-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_of_mem_twist_zero_2b5c0ee4a651
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_of_mem_twist_zero_2b5c0ee4a651
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:10.616973+00:00
-- url     : https://prove2.me/theorems/185a7490-707c-47f8-ac68-14fd67b950fd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Extension Proof mem of mem twist zero 2b5c0ee4a651: P2 M Ground Theory Heights  Heights Kleiman Extension Proof mem of mem twist zero 2b5c0ee4a651
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Extension Proof mem of mem twist zero 2b5c0ee4a651 construction uses the P2 M Ground Theory Heights  Heights Kleiman Extension Proof mem of mem twist zero 2b5c0ee4a651 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L83-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L83-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
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
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_of_mem_twist_zero_2b5c0ee4a651 (F : SubSystem S x E) {J : Chart x} {m : E}
    (hm : m ∈ (F.twist (twistSys S x 0)).sub J) : m ∈ F.sub J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ExtensionProof».«mem_of_mem_twist_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_of_mem_twist_zero_2b5c0ee4a651
