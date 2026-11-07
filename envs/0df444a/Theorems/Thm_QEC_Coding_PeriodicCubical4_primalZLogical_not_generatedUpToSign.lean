-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalZLogical_not_generatedUpToSign
-- name    : QEC.Coding.PeriodicCubical4.primalZLogical_not_generatedUpToSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:34:02.375835+00:00
-- url     : https://prove2.me/theorems/f5ca8421-03f9-421b-8056-94bfc0a6f30a
-- title:
--   Periodic Cubical4: primal ZLogical not generated Up To Sign
-- statement:
--   The primal membrane is non-stabilizer even modulo the binary global-sign convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L424-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L424-L439

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic

theorem QEC.Coding.PeriodicCubical4.primalZLogical_not_generatedUpToSign
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    ¬ InGeneratedStabilizerUpToSign
      (toricGenerator (L := L)) (primalZLogical z₀ w₀) := by sorry
