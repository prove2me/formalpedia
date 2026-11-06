-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_of_not_mem
-- name    : QEC.Semantics.Davies.frequencyComponent_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:13:52.94711+00:00
-- url     : https://prove2.me/theorems/b2ea55c4-d599-4b32-b180-c17fdc28fd9d
-- title:
--   Davies: frequency Component of not mem
-- statement:
--   The Davies construction uses the frequency Component of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L42-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L42-L48

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

theorem QEC.Semantics.Davies.frequencyComponent_of_not_mem (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (ω : ℝ) (hω : ω ∉ frequencies e) :
    frequencyComponent b e A ω = 0 := by sorry
