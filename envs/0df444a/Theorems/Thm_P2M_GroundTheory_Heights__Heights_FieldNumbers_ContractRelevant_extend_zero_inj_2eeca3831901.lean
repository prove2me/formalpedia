-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_extend_zero_inj_2eeca3831901
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_extend_zero_inj_2eeca3831901
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:43.04173+00:00
-- url     : https://prove2.me/theorems/3b5df08e-d517-44c6-9421-e48ffe0f5906
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant extend zero inj 2eeca3831901: P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant extend zero inj 2eeca3831901
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant extend zero inj 2eeca3831901 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant extend zero inj 2eeca3831901 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractRelevant.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractRelevant.lean#L23-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_extend_zero_inj_2eeca3831901 {K K' : Type*} {j : K → K'} (hj : Function.Injective j)
    {x y : K → ℕ} : Function.extend j x 0 = Function.extend j y 0 ↔ x = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ContractRelevant».«extend_zero_inj» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_extend_zero_inj_2eeca3831901
