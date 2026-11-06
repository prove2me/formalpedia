-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_sum
-- name    : QEC.Semantics.Davies.frequencyComponent_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:39.088193+00:00
-- url     : https://prove2.me/theorems/66ea5cf0-16f9-4906-8c5f-809daf920ae0
-- title:
--   Davies: frequency Component sum
-- statement:
--   The Davies construction uses the frequency Component sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L33-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L33-L40

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

theorem QEC.Semantics.Davies.frequencyComponent_sum {κ : Type*} (s : Finset κ)
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V) (ω : ℝ) :
    frequencyComponent b e (∑ k ∈ s, A k) ω =
      ∑ k ∈ s, frequencyComponent b e (A k) ω := by sorry
