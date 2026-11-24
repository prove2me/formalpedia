-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_splitVarEquiv_fst_fb4410ce5862
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_splitVarEquiv_fst_fb4410ce5862
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:09.408002+00:00
-- url     : https://prove2.me/theorems/9b30d4b1-298b-42dd-ae99-99d4ea0d2bbf
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers split Var Equiv fst fb4410ce5862: P2 M Ground Theory Heights  Heights Field Numbers split Var Equiv fst fb4410ce5862
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers split Var Equiv fst fb4410ce5862 construction uses the P2 M Ground Theory Heights  Heights Field Numbers split Var Equiv fst fb4410ce5862 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean#L66-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HomFracDegZeroEqFunField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
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
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_splitVarEquiv_fst_fb4410ce5862 (v : Σ s, splitCoord j ι' s) :
    (splitVarEquiv j ι' v).1 = splitBlockEquiv j v.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«splitVarEquiv_fst» := P2M_GroundTheory_Heights__Heights_FieldNumbers_splitVarEquiv_fst_fb4410ce5862
