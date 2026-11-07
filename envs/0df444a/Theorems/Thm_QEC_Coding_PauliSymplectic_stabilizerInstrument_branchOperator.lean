-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_branchOperator
-- name    : QEC.Coding.PauliSymplectic.stabilizerInstrument_branchOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:21.878807+00:00
-- url     : https://prove2.me/theorems/af994dfa-9456-497e-b94e-86ffdcf4dc55
-- title:
--   Pauli Symplectic: stabilizer Instrument branch Operator
-- statement:
--   A selective branch is literal nondestructive compression `P_λ ρ P_λ`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L241-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L241-L252

import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.stabilizerInstrument_branchOperator
    (P : Binary ι) (outcome : StabilizerOutcome)
    (A : Operator (Qubit.QubitRegister ι)) :
    (stabilizerInstrument P).branchOperator outcome A =
      stabilizerProjector P outcome * A *
        stabilizerProjector P outcome := by sorry
