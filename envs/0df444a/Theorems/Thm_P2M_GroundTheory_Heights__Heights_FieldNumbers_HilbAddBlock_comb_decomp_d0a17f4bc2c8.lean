-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_comb_decomp_d0a17f4bc2c8
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_comb_decomp_d0a17f4bc2c8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:49.42722+00:00
-- url     : https://prove2.me/theorems/5e7eada1-4fd7-568c-97df-e79a924bde3f
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block comb decomp d0a17f4bc2c8: P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block comb decomp d0a17f4bc2c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block comb decomp d0a17f4bc2c8 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block comb decomp d0a17f4bc2c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L103-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L103-L125

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbAddBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
variable {K : Type} [DecidableEq K] {ι : K → Type} {N : ℕ}
variable {F : Type u} [Field F]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_comb_decomp_d0a17f4bc2c8 (μ : (Σ o, addBlock ι N o) →₀ ℕ) :
    comb (μ.comapDomain (addBlockIncl ι N) addBlockIncl_injective.injOn)
      (μ.comapDomain (newVar ι N) newVar_injective.injOn) = μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbAddBlock».«comb_decomp» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_comb_decomp_d0a17f4bc2c8
