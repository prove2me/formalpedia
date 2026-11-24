-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_monomial_comb_34d020dc0e0d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_monomial_comb_34d020dc0e0d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:37.983857+00:00
-- url     : https://prove2.me/theorems/a5ae3aa5-bf8b-4c9c-becb-9702a721c85c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block monomial comb 34d020dc0e0d: P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block monomial comb 34d020dc0e0d
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block monomial comb 34d020dc0e0d construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block monomial comb 34d020dc0e0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L78-L82

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_monomial_comb_34d020dc0e0d (d : (Σ k, ι k) →₀ ℕ) (a : Fin (N + 1) →₀ ℕ) (c : F) :
    monomial (comb d a) c =
      rename (addBlockIncl ι N) (monomial d c) * rename (newVar ι N) (monomial a 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbAddBlock».«monomial_comb» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_monomial_comb_34d020dc0e0d
