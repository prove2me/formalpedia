-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_actualFrequency_zeroHamiltonian
-- name    : QEC.Semantics.Davies.actualFrequency_zeroHamiltonian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:14:06.882455+00:00
-- url     : https://prove2.me/theorems/4dba81fa-a1f2-409d-9aaf-8bac9deeb08b
-- title:
--   Davies: actual Frequency zero Hamiltonian
-- statement:
--   The Davies construction uses the actual Frequency zero Hamiltonian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L147-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L147-L150

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

theorem QEC.Semantics.Davies.actualFrequency_zeroHamiltonian (A : Operator V) (ω : ℝ) :
    actualFrequency 0 LinearMap.IsSymmetric.zero A ω = if 0=ω then A else 0 := by sorry
