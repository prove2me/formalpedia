-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_splitEquiv_monomial_comb_2a61c6c7db83
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_splitEquiv_monomial_comb_2a61c6c7db83
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:43.384601+00:00
-- url     : https://prove2.me/theorems/6a3fd027-30a1-4a57-b552-20df841dd6a9
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block split Equiv monomial comb 2a61c6c7db83: P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block split Equiv monomial comb 2a61
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block split Equiv monomial comb 2a61c6c7db83 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block split Equiv monomial comb 2a61c6c7db83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L85-L88

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_splitEquiv_monomial_comb_2a61c6c7db83 (d : (Σ k, ι k) →₀ ℕ) (a : Fin (N + 1) →₀ ℕ) (c : F) :
    splitEquiv F ι N (monomial (comb d a) c) = monomial a (monomial d c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbAddBlock».«splitEquiv_monomial_comb» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_splitEquiv_monomial_comb_2a61c6c7db83
