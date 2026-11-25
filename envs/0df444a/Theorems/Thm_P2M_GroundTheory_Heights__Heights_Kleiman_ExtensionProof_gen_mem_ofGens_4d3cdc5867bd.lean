-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_gen_mem_ofGens_4d3cdc5867bd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_gen_mem_ofGens_4d3cdc5867bd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:11.765741+00:00
-- url     : https://prove2.me/theorems/20e1fc1e-39de-453e-9074-0a1f3f4ce000
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Extension Proof gen mem of Gens 4d3cdc5867bd: P2 M Ground Theory Heights  Heights Kleiman Extension Proof gen mem of Gens 4d3cdc5867bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Extension Proof gen mem of Gens 4d3cdc5867bd construction uses the P2 M Ground Theory Heights  Heights Kleiman Extension Proof gen mem of Gens 4d3cdc5867bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L187-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L187-L189

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_gen_mem_ofGens_4d3cdc5867bd {ι : Type} [Fintype ι] (deg : ι → ℤ) (gen : ι → E) (k : ι) :
    gen k ∈ (ofGens (S := S) (x := x) deg gen).piece (deg k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ExtensionProof».«gen_mem_ofGens» := P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_gen_mem_ofGens_4d3cdc5867bd
