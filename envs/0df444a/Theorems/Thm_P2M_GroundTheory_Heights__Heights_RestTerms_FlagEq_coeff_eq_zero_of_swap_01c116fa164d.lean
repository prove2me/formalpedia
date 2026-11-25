-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_eq_zero_of_swap_01c116fa164d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_eq_zero_of_swap_01c116fa164d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:30.451371+00:00
-- url     : https://prove2.me/theorems/9cdf10f8-ed09-4ece-8858-c55e28e32221
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff eq zero of swap 01c116fa164d: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff eq zero of swap 01c116fa164d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff eq zero of swap 01c116fa164d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff eq zero of swap 01c116fa164d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L90-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L90-L118

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_eq_zero_of_swap_01c116fa164d {f N : ℕ} (A : MvPolynomial (Fin f × Fin N) ℝ)
    (hA : ∀ u : Fin f → Equiv.Perm (Fin N),
      rename (Equiv.prodCongrRight u) A = ((permSign f N u : ℤ) : ℝ) • A)
    (β : Fin f × Fin N →₀ ℕ) (τ : Fin f) (i i' : Fin N) (hii : i ≠ i')
    (hβ : β (τ, i) = β (τ, i')) : coeff β A = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«coeff_eq_zero_of_swap» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_eq_zero_of_swap_01c116fa164d
