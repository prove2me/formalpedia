-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue_proof_c1792c9c7dad
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue_proof_c1792c9c7dad
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:11:12.727368+00:00
-- url     : https://prove2.me/theorems/102d2bb6-2219-52b0-999f-5b7df8924175
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Deg Zero Loc Residue proof c1792c9c7dad: P2 M Ground Theory Heights  Heights Field Numbers Deg Zero Loc Residue proof c1792c9c7dad
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Deg Zero Loc Residue proof c1792c9c7dad construction uses the P2 M Ground Theory Heights  Heights Field Numbers Deg Zero Loc Residue proof c1792c9c7dad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocResidue.lean#L92-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocResidue.lean#L92-L140

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocResidue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocQuot_proof_f2e3f8a36e28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_proof_0aacacc92e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RelevantPrimeDimGe_proof_f3a1f51a2659

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
set_option synthInstance.maxHeartbeats 400000
open GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue
variable {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
local notation "fr" Q:max h:max =>
  algebraMap (_ ⧸ Q) (FractionRing (_ ⧸ Q)) (Ideal.Quotient.mk Q h)
variable {P W : Ideal (MRing ι F)} [P.IsPrime] [W.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue_proof_c1792c9c7dad : DegZeroLocResidue.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«DegZeroLocResidue».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue_proof_c1792c9c7dad
