-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_pairwise_openSeparatedByGap
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_pairwise_openSeparatedByGap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:32:11.058258+00:00
-- url     : https://prove2.me/theorems/e97356fd-d7f2-47df-a5f6-14b495ae203b
-- title:
--   Strip Geometry: first Parity pairwise open Separated By Gap
-- statement:
--   Every two first-parity strips have the required directed coordinate gap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L412-L440
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L412-L440

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_pairwise_openSeparatedByGap
    (L r start : Nat) (widths : List Nat)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (firstParity (openStripListAux L start widths)).Pairwise
      (OpenSeparatedByGap r) := by sorry
