-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue___apply_01e9e3406336
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue___apply_01e9e3406336
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:04:28.610466+00:00
-- url     : https://prove2.me/theorems/eebf50ab-3294-5cb8-8462-cc4adb418c7a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Deg Zero Loc Residue   apply 01e9e3406336: P2 M Ground Theory Heights  Heights Field Numbers Deg Zero Loc Residue   apply 01e9e3406336
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Deg Zero Loc Residue   apply 01e9e3406336 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Deg Zero Loc Residue   apply 01e9e3406336 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocResidue.lean#L86-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocResidue.lean#L86-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocResidue
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue___apply_01e9e3406336 (hPW : P ≤ W) (x : degZeroLoc P {W}) : ρ hPW x = res P W x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«DegZeroLocResidue».«ρ_apply» := P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue___apply_01e9e3406336
