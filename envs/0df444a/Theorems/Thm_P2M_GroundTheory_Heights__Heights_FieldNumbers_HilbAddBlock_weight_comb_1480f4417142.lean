-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_weight_comb_1480f4417142
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_weight_comb_1480f4417142
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:55.989605+00:00
-- url     : https://prove2.me/theorems/a0a04944-b61b-5201-b9ff-db229102bd83
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block weight comb 1480f4417142: P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block weight comb 1480f4417142
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block weight comb 1480f4417142 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block weight comb 1480f4417142 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L127-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L127-L146

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_weight_comb_1480f4417142 (d : (Σ k, ι k) →₀ ℕ) (a : Fin (N + 1) →₀ ℕ) :
    Finsupp.weight (blockWeight (addBlock ι N)) (comb d a) =
      fun o => Option.elim o (∑ j, a j) (Finsupp.weight (blockWeight ι) d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbAddBlock».«weight_comb» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_weight_comb_1480f4417142
