-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_HammingWeight_pairings_le_of_pairwise_disjoint
-- name    : QEC.Coding.PeriodicCubical4.HammingWeight_pairings_le_of_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:27:59.756575+00:00
-- url     : https://prove2.me/theorems/8374281a-68ab-463c-b4f4-6c0180cf4c41
-- title:
--   Periodic Cubical4: Hamming Weight pairings le of pairwise disjoint
-- statement:
--   Pairings against pairwise support-disjoint fibers cannot contain more
--   nonzero coordinates than the word being paired.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L340-L381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L340-L381

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.HammingWeight_pairings_le_of_pairwise_disjoint
    {FiberIndex CellIndex : Type*}
    [Fintype FiberIndex] [DecidableEq FiberIndex]
    [Fintype CellIndex] [DecidableEq CellIndex]
    (fiber : FiberIndex → Word (ZMod 2) CellIndex)
    (u : Word (ZMod 2) CellIndex)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (hammingSupport (fiber i)) (hammingSupport (fiber j))) :
    HammingWeight (fun i => wordPairing (fiber i) u) ≤ HammingWeight u := by sorry
