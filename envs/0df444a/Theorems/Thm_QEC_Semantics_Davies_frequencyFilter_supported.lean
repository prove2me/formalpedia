-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyFilter_supported
-- name    : QEC.Semantics.Davies.frequencyFilter_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:35.536697+00:00
-- url     : https://prove2.me/theorems/bdeb93c8-b7ab-4189-86f5-dca0a2b966d0
-- title:
--   Davies: frequency Filter supported
-- statement:
--   The Davies construction uses the frequency Filter supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L204-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L204-L213

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

theorem QEC.Semantics.Davies.frequencyFilter_supported (S : FiniteSubsystem q)
    (H A : Operator (Qubit.QubitRegister q)) (ω : ℝ) (l : List ℝ)
    (hH : S.OperatorSupportedOnRegister H) (hA : S.OperatorSupportedOnRegister A) :
    S.OperatorSupportedOnRegister (frequencyFilter H ω l A) := by sorry
