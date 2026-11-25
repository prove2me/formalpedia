-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_eq_param_ece8966a1178
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_eq_param_ece8966a1178
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:21.629353+00:00
-- url     : https://prove2.me/theorems/481b19c1-85d0-4931-9ef8-40ccd758d927
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense eq param ece8966a1178: P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense eq param ece8966a1178
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense eq param ece8966a1178 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense eq param ece8966a1178 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L59-L67

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
omit hσ hJ

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_eq_param_ece8966a1178
    (hfix : ∀ u, hf σ J u e = 0 → hf σ J u f = 0 → perpProj σ J e f u = u)
    {M : Matrix (Fin N) (Fin N) R} (hM : M ∈ eichAlong σ J e f) : ∃ p, M = param σ J e f κ p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerDense».«eq_param» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_eq_param_ece8966a1178
