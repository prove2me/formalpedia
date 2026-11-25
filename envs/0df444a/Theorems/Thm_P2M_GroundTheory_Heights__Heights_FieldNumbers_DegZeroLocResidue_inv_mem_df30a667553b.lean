-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue_inv_mem_df30a667553b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue_inv_mem_df30a667553b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:53:28.99772+00:00
-- url     : https://prove2.me/theorems/e3bc3797-8278-4491-95ff-f4138f0aede4
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Deg Zero Loc Residue inv mem df30a667553b: P2 M Ground Theory Heights  Heights Field Numbers Deg Zero Loc Residue inv mem df30a667553b
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Deg Zero Loc Residue inv mem df30a667553b construction uses the P2 M Ground Theory Heights  Heights Field Numbers Deg Zero Loc Residue inv mem df30a667553b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocResidue.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocResidue.lean#L88-L90

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue_inv_mem_df30a667553b (hPW : P ≤ W) {b : K → ℕ} {f g : MRing ι F} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g b) (hfW : f ∉ W) : fr P g / fr P f ∈ degZeroLoc P {W} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«DegZeroLocResidue».«inv_mem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue_inv_mem_df30a667553b
