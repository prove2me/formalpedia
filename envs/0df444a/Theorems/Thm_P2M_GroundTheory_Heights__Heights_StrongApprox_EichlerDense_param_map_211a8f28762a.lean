-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_param_map_211a8f28762a
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_param_map_211a8f28762a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:12.414801+00:00
-- url     : https://prove2.me/theorems/fbd68db3-3b96-5ffc-bb11-70f41d62fff4
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense param map 211a8f28762a: P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense param map 211a8f28762a
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense param map 211a8f28762a construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense param map 211a8f28762a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L35-L43

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_param_map_211a8f28762a {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (e f : Fin N → R) (κ : R)
    (p : (Fin N → R) × R) :
    (param σ J e f κ p).map φ = param σ' (J.map φ) (φ ∘ e) (φ ∘ f) (φ κ) (φ ∘ p.1, φ p.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerDense».«param_map» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_param_map_211a8f28762a
