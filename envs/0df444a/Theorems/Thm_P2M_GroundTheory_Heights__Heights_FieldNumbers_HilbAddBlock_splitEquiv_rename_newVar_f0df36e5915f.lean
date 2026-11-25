-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_splitEquiv_rename_newVar_f0df36e5915f
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_splitEquiv_rename_newVar_f0df36e5915f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:09.385449+00:00
-- url     : https://prove2.me/theorems/50e1b609-db54-4cb7-be10-209e75f51489
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block split Equiv rename new Var f0df36e5915f: P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block split Equiv rename new Var f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block split Equiv rename new Var f0df36e5915f construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block split Equiv rename new Var f0df36e5915f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L63-L72

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_splitEquiv_rename_newVar_f0df36e5915f (q : MvPolynomial (Fin (N + 1)) F) :
    splitEquiv F ι N (rename (newVar ι N) q) = map C q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbAddBlock».«splitEquiv_rename_newVar» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_splitEquiv_rename_newVar_f0df36e5915f
