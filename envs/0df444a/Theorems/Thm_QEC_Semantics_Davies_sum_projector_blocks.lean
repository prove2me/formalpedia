-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_sum_projector_blocks
-- name    : QEC.Semantics.Davies.sum_projector_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:27:31.34431+00:00
-- url     : https://prove2.me/theorems/a254c15c-d144-4891-9f1a-757d23a94ba0
-- title:
--   Davies: sum projector blocks
-- statement:
--   The Davies construction uses the sum projector blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L477-L481
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L477-L481

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

theorem QEC.Semantics.Davies.sum_projector_blocks (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) :
    (∑ E ∈ energyValues e, ∑ F ∈ energyValues e,
      energyProjector b e E * A * energyProjector b e F) = A := by sorry
