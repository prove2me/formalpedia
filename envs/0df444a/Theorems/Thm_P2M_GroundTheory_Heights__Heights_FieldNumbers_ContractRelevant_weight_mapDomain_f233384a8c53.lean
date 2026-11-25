-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_weight_mapDomain_f233384a8c53
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_weight_mapDomain_f233384a8c53
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:47.267744+00:00
-- url     : https://prove2.me/theorems/e411953e-415f-49e6-9249-3c4e1867fcbc
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant weight map Domain f233384a8c53: P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant weight map Domain f233384a8c53
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant weight map Domain f233384a8c53 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant weight map Domain f233384a8c53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractRelevant.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractRelevant.lean#L32-L48

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
variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {ι : K → Type*} {ι' : K' → Type*}
  {j : K → K'} {g : (Σ k, ι k) → (Σ k, ι' k)} (hgj : ∀ v, (g v).1 = j v.1)
include hgj

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_weight_mapDomain_f233384a8c53 (hj : Function.Injective j) (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain g d) =
      Function.extend j (Finsupp.weight (blockWeight ι) d) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ContractRelevant».«weight_mapDomain» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_weight_mapDomain_f233384a8c53
