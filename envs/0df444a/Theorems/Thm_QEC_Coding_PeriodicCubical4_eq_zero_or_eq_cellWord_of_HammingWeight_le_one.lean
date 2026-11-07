-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_eq_zero_or_eq_cellWord_of_HammingWeight_le_one
-- name    : QEC.Coding.PeriodicCubical4.eq_zero_or_eq_cellWord_of_HammingWeight_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:29:39.722352+00:00
-- url     : https://prove2.me/theorems/80f2c730-a5db-4324-a6b6-a5727fb1a1ed
-- title:
--   Periodic Cubical4: eq zero or eq cell Word of Hamming Weight le one
-- statement:
--   Over `ZMod 2`, a word of Hamming weight at most one is either zero or one
--   cell word.  This extracts the actual local increment rather than assuming a
--   chosen plaquette.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L495-L529
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L495-L529

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.eq_zero_or_eq_cellWord_of_HammingWeight_le_one
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (m : Word (ZMod 2) Index) (hm : HammingWeight m ≤ 1) :
    m = 0 ∨ ∃ i, m = cellWord i := by sorry
