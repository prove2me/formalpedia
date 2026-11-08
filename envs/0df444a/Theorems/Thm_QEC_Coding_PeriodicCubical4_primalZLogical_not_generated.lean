-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalZLogical_not_generated
-- name    : QEC.Coding.PeriodicCubical4.primalZLogical_not_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:45:52.260207+00:00
-- url     : https://prove2.me/theorems/56bd2975-04b4-4621-8a25-fb32a9ebcd1d
-- title:
--   Periodic Cubical4: primal ZLogical not generated
-- statement:
--   The primal membrane normalizer element is not in the selected stabilizer closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L442-L447
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L442-L447

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic

theorem QEC.Coding.PeriodicCubical4.primalZLogical_not_generated {L : Nat} [NeZero L] [Fact (1 < L)]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    ¬ GeneratedStabilizer (toricGenerator (L := L)) (primalZLogical z₀ w₀) := by sorry
