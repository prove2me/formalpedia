-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_stabilizerGoodSyndromeProtectedObservable
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.stabilizerGoodSyndromeProtectedObservable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:37:00.24148+00:00
-- url     : https://prove2.me/theorems/0376c25f-8ed6-4cc2-910a-403780b18488
-- title:
--   Decoder Dressed Logical: stabilizer Good Syndrome Protected Observable
-- statement:
--   The complete stabilizer good-syndrome adapter used downstream by M11.  Every
--   property in the conclusion is derived above from deterministic correction,
--   the stabilizer normalizer laws, and the source-exact goodness predicate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L580-L618
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L580-L618

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
open QEC.Coding.StabilizerCode.DecoderDressedLogical
variable {H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)}

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.stabilizerGoodSyndromeProtectedObservable
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    IsStarProjection (D.goodSyndromeProjector elementaryErrors) ∧
      Commute (D.goodSyndromeProjector elementaryErrors) D.dressedX ∧
      Commute (D.goodSyndromeProjector elementaryErrors) D.dressedZ ∧
      Commute (D.goodSyndromeProjector elementaryErrors) H.operator ∧
      D.goodSyndromeProjector elementaryErrors * D.dressedX *
          D.goodSyndromeProjector elementaryErrors =
        D.dressedX * D.goodSyndromeProjector elementaryErrors ∧
      D.goodSyndromeProjector elementaryErrors * D.dressedZ *
          D.goodSyndromeProjector elementaryErrors =
        D.dressedZ * D.goodSyndromeProjector elementaryErrors ∧
      (∀ error ∈ elementaryErrors,
        (toHermitianQubitOperator error * D.dressedX -
            D.dressedX * toHermitianQubitOperator error) *
          D.goodSyndromeProjector elementaryErrors = 0 ∧
        (toHermitianQubitOperator error * D.dressedZ -
            D.dressedZ * toHermitianQubitOperator error) *
          D.goodSyndromeProjector elementaryErrors = 0) ∧
      ∀ rhoBeta : DensityOperator (Qubit.QubitRegister ι),
        LinearMap.trace Complex (Qubit.QubitRegister ι)
            ((1 - D.goodSyndromeProjector elementaryErrors) *
              rhoBeta.toOperator) =
          D.badSyndromeGibbsWeight elementaryErrors rhoBeta := by sorry
