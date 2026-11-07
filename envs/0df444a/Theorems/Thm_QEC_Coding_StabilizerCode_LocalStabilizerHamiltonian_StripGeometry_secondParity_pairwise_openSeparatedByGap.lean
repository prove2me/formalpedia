-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_pairwise_openSeparatedByGap
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_pairwise_openSeparatedByGap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:35:43.596406+00:00
-- url     : https://prove2.me/theorems/921fb8b4-9c5c-40a6-97f6-e2e64f865dc2
-- title:
--   Strip Geometry: second Parity pairwise open Separated By Gap
-- statement:
--   The directed coordinate-gap form for the second parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L455-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L455-L466

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_pairwise_openSeparatedByGap
    (L r start : Nat) (widths : List Nat)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (secondParity (openStripListAux L start widths)).Pairwise
      (OpenSeparatedByGap r) := by sorry
