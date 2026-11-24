-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_hf_map_ce22e49943f2
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_hf_map_ce22e49943f2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:13.970414+00:00
-- url     : https://prove2.me/theorems/a0ae5576-7a82-46fa-bef5-ed67e3cae046
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense hf map ce22e49943f2: P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense hf map ce22e49943f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense hf map ce22e49943f2 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense hf map ce22e49943f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L24-L27

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
variable {R : Type*} [CommRing R] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_hf_map_ce22e49943f2 {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (x y : Fin N → R) :
    hf σ' (J.map φ) (φ ∘ x) (φ ∘ y) = φ (hf σ J x y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerDense».«hf_map» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_hf_map_ce22e49943f2
