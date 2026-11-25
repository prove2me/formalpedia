-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_param_mem_17e5ebbedd81
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_param_mem_17e5ebbedd81
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:05.205828+00:00
-- url     : https://prove2.me/theorems/75c15712-cdd0-5dc0-afc4-88c456145e2a
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense param mem 17e5ebbedd81: P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense param mem 17e5ebbedd81
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense param mem 17e5ebbedd81 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense param mem 17e5ebbedd81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L49-L55

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
variable {σ : R →+* R} (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin N) (Fin N) R} (hJ : Jᵀ = J.map σ)
  {e f : Fin N → R} {κ : R} (hκ : κ + κ = 1) (hσκ : σ κ = κ)
include hσ hJ hκ hσκ

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_param_mem_17e5ebbedd81
    (hP : ∀ u, hf σ J (perpProj σ J e f u) e = 0 ∧ hf σ J (perpProj σ J e f u) f = 0)
    (p : (Fin N → R) × R) : param σ J e f κ p ∈ eichAlong σ J e f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerDense».«param_mem» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_param_mem_17e5ebbedd81
