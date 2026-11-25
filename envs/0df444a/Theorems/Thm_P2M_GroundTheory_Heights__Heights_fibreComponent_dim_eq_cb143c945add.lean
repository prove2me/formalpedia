-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreComponent_dim_eq_cb143c945add
-- name    : P2M_GroundTheory_Heights__Heights_fibreComponent_dim_eq_cb143c945add
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:06.677708+00:00
-- url     : https://prove2.me/theorems/23ac51ab-e880-5662-8a03-17ac0e4ec59a
-- title:
--   P2 M Ground Theory Heights  Heights fibre Component dim eq cb143c945add: P2 M Ground Theory Heights  Heights fibre Component dim eq cb143c945add
-- statement:
--   The P2 M Ground Theory Heights  Heights fibre Component dim eq cb143c945add construction uses the P2 M Ground Theory Heights  Heights fibre Component dim eq cb143c945add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PFibreCompDimZ.lean#L29-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PFibreCompDimZ.lean#L29-L74

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

theorem P2M_GroundTheory_Heights__Heights_fibreComponent_dim_eq_cb143c945add (hP : P.IsPrime) (hPC : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥)
    {p : ℕ} (hp : p.Prime) {W : Ideal (MvPolynomial σ ℤ)}
    (hW : W ∈ (P ⊔ Ideal.span {(C (p : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes) :
    ∃ m : ℕ, ringKrullDim (MvPolynomial σ ℤ ⧸ W) = m ∧ ∀ q : ℕ, q.Prime →
      ∀ W' ∈ (P ⊔ Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes,
        ringKrullDim (MvPolynomial σ ℤ ⧸ W') = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fibreComponent_dim_eq» := P2M_GroundTheory_Heights__Heights_fibreComponent_dim_eq_cb143c945add
