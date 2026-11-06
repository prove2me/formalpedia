-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_commutator
-- name    : QEC.Semantics.Davies.frequencyComponent_commutator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:26:42.969958+00:00
-- url     : https://prove2.me/theorems/b1289722-c28d-414c-86e8-580b7b99cf36
-- title:
--   Davies: frequency Component commutator
-- statement:
--   The Davies construction uses the frequency Component commutator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L337-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L337-L350

import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.Davies.frequencyComponent_commutator (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (ω : ℝ) :
    diagonal b e * frequencyComponent b e A ω -
      frequencyComponent b e A ω * diagonal b e =
      (-ω : ℂ) • frequencyComponent b e A ω := by sorry
