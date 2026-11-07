-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualXLogical_not_generated
-- name    : QEC.Coding.PeriodicCubical4.dualXLogical_not_generated
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:48:19.79036+00:00
-- url     : https://prove2.me/theorems/8a3c81f3-140c-4f82-b5f8-fbc3aa16227a
-- title:
--   Periodic Cubical4: dual XLogical not generated
-- statement:
--   The dual membrane normalizer element is not in the selected stabilizer closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L468-L473
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L468-L473

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic

theorem QEC.Coding.PeriodicCubical4.dualXLogical_not_generated {L : Nat} [NeZero L] [Fact (1 < L)]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    ¬ GeneratedStabilizer (toricGenerator (L := L)) (dualXLogical x₀ y₀) := by sorry
