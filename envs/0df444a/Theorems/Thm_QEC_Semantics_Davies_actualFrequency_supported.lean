-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_actualFrequency_supported
-- name    : QEC.Semantics.Davies.actualFrequency_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:13:37.741124+00:00
-- url     : https://prove2.me/theorems/a25e509a-108b-4585-9142-d7ae6c6eebf9
-- title:
--   Davies: actual Frequency supported
-- statement:
--   Real tensor support of a spectral component, with the local witness constructed by filtering.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L216-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L216-L230

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {q : Type} [Fintype q] [DecidableEq q]

theorem QEC.Semantics.Davies.actualFrequency_supported (S : FiniteSubsystem q)
    (H A : Operator (Qubit.QubitRegister q)) (hH : H.IsSymmetric)
    (hsH : S.OperatorSupportedOnRegister H) (hsA : S.OperatorSupportedOnRegister A) (ω : ℝ) :
    S.OperatorSupportedOnRegister (actualFrequency H hH A ω) := by sorry
