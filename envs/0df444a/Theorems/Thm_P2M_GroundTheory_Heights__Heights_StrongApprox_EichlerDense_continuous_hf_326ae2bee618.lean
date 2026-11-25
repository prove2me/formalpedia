-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_continuous_hf_326ae2bee618
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_continuous_hf_326ae2bee618
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:25.70224+00:00
-- url     : https://prove2.me/theorems/adef06e3-1845-48c4-8ddf-3150eb739940
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense continuous hf 326ae2bee618: P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense continuous hf 326ae2bee618
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense continuous hf 326ae2bee618 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense continuous hf 326ae2bee618 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L76-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
variable {X : Type*} [TopologicalSpace X] {S : Type*} [CommRing S] [TopologicalSpace S]
  [IsTopologicalRing S] {N : ℕ} {σ : S →+* S}

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_continuous_hf_326ae2bee618 (hσ : Continuous σ) (J : Matrix (Fin N) (Fin N) S) {x y : X → Fin N → S}
    (hx : Continuous x) (hy : Continuous y) : Continuous fun t => hf σ J (x t) (y t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerDense».«continuous_hf» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_continuous_hf_326ae2bee618
