-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_entry_energyDifference
-- name    : QEC.Semantics.Davies.entry_energyDifference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:13:59.062652+00:00
-- url     : https://prove2.me/theorems/ed5f2725-b1ac-4800-858d-dc2211b50322
-- title:
--   Davies: entry energy Difference
-- statement:
--   The Davies construction uses the entry energy Difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L17-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L17-L23

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

theorem QEC.Semantics.Davies.entry_energyDifference (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (i j : ι) :
    entry b (energyDifference (diagonal b e) A) i j =
      ((e j-e i : ℝ) : ℂ) * entry b A i j := by sorry
