-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_le_of_fibreComponents_a61df9f7bb47
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_le_of_fibreComponents_a61df9f7bb47
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:14:51.586529+00:00
-- url     : https://prove2.me/theorems/dc44f018-8114-5e4f-9fad-1aae702b4dbb
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim le of fibre Components a61df9f7bb47: P2 M Ground Theory Heights  Heights ring Krull Dim le of fibre Components a61df9f7bb47
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim le of fibre Components a61df9f7bb47 construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim le of fibre Components a61df9f7bb47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PFibreCompDimZ.lean#L93-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PFibreCompDimZ.lean#L93-L119

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

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_le_of_fibreComponents_a61df9f7bb47 (k : WithBot ℕ∞)
    (h : ∀ q : ℕ, q.Prime → ∀ W ∈ (P ⊔ Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes,
      ringKrullDim (MvPolynomial σ ℤ ⧸ W) ≤ k) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ P) ≤ k + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_le_of_fibreComponents» := P2M_GroundTheory_Heights__Heights_ringKrullDim_le_of_fibreComponents_a61df9f7bb47
