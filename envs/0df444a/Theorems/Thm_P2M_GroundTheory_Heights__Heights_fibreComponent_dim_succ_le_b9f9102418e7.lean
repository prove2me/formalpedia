-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreComponent_dim_succ_le_b9f9102418e7
-- name    : P2M_GroundTheory_Heights__Heights_fibreComponent_dim_succ_le_b9f9102418e7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:20:13.501749+00:00
-- url     : https://prove2.me/theorems/29efc37e-c8ca-4b6c-b634-8ec7ef96b408
-- title:
--   P2 M Ground Theory Heights  Heights fibre Component dim succ le b9f9102418e7: P2 M Ground Theory Heights  Heights fibre Component dim succ le b9f9102418e7
-- statement:
--   The P2 M Ground Theory Heights  Heights fibre Component dim succ le b9f9102418e7 construction uses the P2 M Ground Theory Heights  Heights fibre Component dim succ le b9f9102418e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PFibreCompDimZ.lean#L78-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PFibreCompDimZ.lean#L78-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsFibreCompDimZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_OfChartPointSecPointSpecChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PFibreCompDimZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial IsDedekindDomain
variable {σ : Type} [Fintype σ] {P : Ideal (MvPolynomial σ ℤ)}
omit [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_fibreComponent_dim_succ_le_b9f9102418e7 (hP : P.IsPrime) (hPC : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥)
    {p : ℕ} (hp : p.Prime) {W : Ideal (MvPolynomial σ ℤ)}
    (hW : W ∈ (P ⊔ Ideal.span {(C (p : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ W) + 1 ≤ ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fibreComponent_dim_succ_le» := P2M_GroundTheory_Heights__Heights_fibreComponent_dim_succ_le_b9f9102418e7
