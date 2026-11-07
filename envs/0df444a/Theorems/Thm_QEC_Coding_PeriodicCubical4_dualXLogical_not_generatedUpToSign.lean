-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualXLogical_not_generatedUpToSign
-- name    : QEC.Coding.PeriodicCubical4.dualXLogical_not_generatedUpToSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:34:21.56667+00:00
-- url     : https://prove2.me/theorems/4a79e007-f1db-4ea6-bb5a-8f5c926869d5
-- title:
--   Periodic Cubical4: dual XLogical not generated Up To Sign
-- statement:
--   The dual membrane is non-stabilizer even modulo the binary global-sign convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L450-L465
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L450-L465

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic

theorem QEC.Coding.PeriodicCubical4.dualXLogical_not_generatedUpToSign
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (x₀ y₀ z₀ w₀ : ZMod L) :
    ¬ InGeneratedStabilizerUpToSign
      (toricGenerator (L := L)) (dualXLogical x₀ y₀) := by sorry
