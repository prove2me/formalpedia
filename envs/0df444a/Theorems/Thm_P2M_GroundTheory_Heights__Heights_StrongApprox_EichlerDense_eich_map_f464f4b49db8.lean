-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_eich_map_f464f4b49db8
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_eich_map_f464f4b49db8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:28.876898+00:00
-- url     : https://prove2.me/theorems/4a4fb13d-be4c-4d08-b90c-6c99eff7d26d
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense eich map f464f4b49db8: P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense eich map f464f4b49db8
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense eich map f464f4b49db8 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense eich map f464f4b49db8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L29-L33

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_eich_map_f464f4b49db8 {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (e u : Fin N → R) (c : R) :
    (eich σ J e u c).map φ = eich σ' (J.map φ) (φ ∘ e) (φ ∘ u) (φ c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerDense».«eich_map» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_eich_map_f464f4b49db8
