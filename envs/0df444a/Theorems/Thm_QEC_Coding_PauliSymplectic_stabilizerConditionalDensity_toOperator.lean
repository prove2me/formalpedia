-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
-- name    : QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:26.836107+00:00
-- url     : https://prove2.me/theorems/1689aa4a-d35d-44c4-b321-a7ad8ca30534
-- title:
--   Pauli Symplectic: stabilizer Conditional Density to Operator
-- statement:
--   The Pauli Symplectic construction uses the stabilizer Conditional Density to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L288-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L288-L298

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

theorem QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
    (P : Binary ι) (outcome : StabilizerOutcome)
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (hpos : 0 < (stabilizerInstrument P).bornWeight outcome rho) :
    (stabilizerConditionalDensity P outcome rho hpos).toOperator =
      (((stabilizerInstrument P).bornWeight outcome rho : Complex)⁻¹) •
        (stabilizerProjector P outcome * rho.toOperator *
          stabilizerProjector P outcome) := by sorry
