-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_open_pairwise_intervalSeparated
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_open_pairwise_intervalSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:35:41.918813+00:00
-- url     : https://prove2.me/theorems/d6a299ef-9a80-4060-bc24-42e5d0fc7cdf
-- title:
--   Strip Geometry: first Parity open pairwise interval Separated
-- statement:
--   Every two first-parity strips are separated from open intervals of range `r`
--   when each intervening strip has width at least `r - 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L446-L452
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L446-L452

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_open_pairwise_intervalSeparated
    (L r start : Nat) (widths : List Nat)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (firstParity (openStripListAux L start widths)).Pairwise
      (OpenIntervalSeparated L r) := by sorry
