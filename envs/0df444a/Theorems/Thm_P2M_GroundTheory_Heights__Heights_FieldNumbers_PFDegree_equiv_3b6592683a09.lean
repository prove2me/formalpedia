-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFDegree_equiv_3b6592683a09
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFDegree_equiv_3b6592683a09
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:27.120924+00:00
-- url     : https://prove2.me/theorems/d8cebf40-8596-427e-86a5-9c33a3fe4db0
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFDegree equiv 3b6592683a09: P2 M Ground Theory Heights  Heights Field Numbers PFDegree equiv 3b6592683a09
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFDegree equiv 3b6592683a09 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFDegree equiv 3b6592683a09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean#L141-L145

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFDegree_equiv_3b6592683a09 (h₁ : RenameMultiHomog.Statement.{u})
    (h₂ : RenameIntNum.Statement.{u}) (h₃ : RenameMultiProjPrime.Statement.{u})
    (h₄ : SplitRelDeg.Statement.{u}) :
    ProjectionFormulaDegree.Statement.{u} ↔ IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFDegree».«equiv» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFDegree_equiv_3b6592683a09
