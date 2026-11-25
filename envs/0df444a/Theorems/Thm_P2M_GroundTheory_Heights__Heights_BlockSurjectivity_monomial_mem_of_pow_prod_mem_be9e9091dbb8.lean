-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_monomial_mem_of_pow_prod_mem_be9e9091dbb8
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_monomial_mem_of_pow_prod_mem_be9e9091dbb8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:51.114461+00:00
-- url     : https://prove2.me/theorems/872813a5-eeed-447c-9aa4-ef82edaefbf2
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity monomial mem of pow prod mem be9e9091dbb8: P2 M Ground Theory Heights  Heights Block Surjectivity monomial mem of pow prod mem be9e9091dbb8
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity monomial mem of pow prod mem be9e9091dbb8 construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity monomial mem of pow prod mem be9e9091dbb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L210-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L210-L253

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_monomial_mem_of_pow_prod_mem_be9e9091dbb8 {J : Ideal (MvPolynomial (Coord n) ℂ)} {k₀ : ι} {N : ℕ}
    (hJN : ∀ c : (k : ι) → Fin (n k + 1),
      (∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ)) ^ N ∈ J) :
    ∀ μ ∈ offMonos n k₀ (Fintype.card (Coord n) * N), (monomial μ 1 : MvPolynomial (Coord n) ℂ) ∈ J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«monomial_mem_of_pow_prod_mem» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_monomial_mem_of_pow_prod_mem_be9e9091dbb8
