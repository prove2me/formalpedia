-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_fibreLift_075fadd65d1e
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_fibreLift_075fadd65d1e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:53:44.433431+00:00
-- url     : https://prove2.me/theorems/b246a9fe-b11c-55b3-b919-871d4d7c3b8b
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers exists fibre Lift 075fadd65d1e: P2 M Ground Theory Heights  Heights Field Numbers exists fibre Lift 075fadd65d1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers exists fibre Lift 075fadd65d1e construction uses the P2 M Ground Theory Heights  Heights Field Numbers exists fibre Lift 075fadd65d1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsSemilocalLengthSum.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsSemilocalLengthSum.lean#L26-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLengthSum
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
variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_fibreLift_075fadd65d1e (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) (α : degZeroLoc (contractPrime j P') {W}) :
    ∃ β : (W' : Ideal (MRing ι' F)) → degZeroLoc P' {W'},
      ∀ W' ∈ fibrePrimes j P' W,
        (β W' : FractionRing (MRing ι' F ⧸ P')) = contractFracMap j P' (α : _) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«exists_fibreLift» := P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_fibreLift_075fadd65d1e
