-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_entry_frequencyFilter
-- name    : QEC.Semantics.Davies.entry_frequencyFilter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:23.342053+00:00
-- url     : https://prove2.me/theorems/5d5b57e2-4871-47f1-bad8-4be9420adca3
-- title:
--   Davies: entry frequency Filter
-- statement:
--   The Davies construction uses the entry frequency Filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L159-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L159-L172

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

theorem QEC.Semantics.Davies.entry_frequencyFilter (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (ω : ℝ) (l : List ℝ) (A : Operator V) (i j : ι) :
    entry b (frequencyFilter (diagonal b e) ω l A) i j =
      (l.map (fun ν => (((ω-ν : ℝ) : ℂ)⁻¹) * ((e j-e i-ν : ℝ) : ℂ))).prod *
        entry b A i j := by sorry
