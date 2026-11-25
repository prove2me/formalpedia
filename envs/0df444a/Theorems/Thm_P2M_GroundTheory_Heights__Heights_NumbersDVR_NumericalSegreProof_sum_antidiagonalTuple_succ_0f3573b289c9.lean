-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_sum_antidiagonalTuple_succ_0f3573b289c9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_sum_antidiagonalTuple_succ_0f3573b289c9
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:37.303962+00:00
-- url     : https://prove2.me/theorems/fa19f2df-2dcd-4d80-91f0-72e216f87cd2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof sum antidiagonal Tuple succ 0f3573b289c9: P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof sum antidiagonal T
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof sum antidiagonal Tuple succ 0f3573b289c9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof sum antidiagonal Tuple succ 0f3573b289c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L16-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L16-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_sum_antidiagonalTuple_succ_0f3573b289c9 {A : Type*} [AddCommMonoid A] (i c : ℕ)
    (f : (Fin (i + 1) → ℕ) → A) :
    ∑ α ∈ Finset.Nat.antidiagonalTuple (i + 1) (c + 1), f α =
      ∑ α ∈ Finset.Nat.antidiagonalTuple i (c + 1), f (Fin.snoc α 0) +
        ∑ β ∈ Finset.Nat.antidiagonalTuple (i + 1) c,
          f (Function.update β (Fin.last i) (β (Fin.last i) + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NumericalSegreProof».«sum_antidiagonalTuple_succ» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_sum_antidiagonalTuple_succ_0f3573b289c9
