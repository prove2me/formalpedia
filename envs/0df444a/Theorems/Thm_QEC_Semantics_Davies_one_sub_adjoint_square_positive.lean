-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_one_sub_adjoint_square_positive
-- name    : QEC.Semantics.Davies.one_sub_adjoint_square_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:28:22.793326+00:00
-- url     : https://prove2.me/theorems/f4eca764-48d8-44e2-8777-582a82d9ac81
-- title:
--   Davies: one sub adjoint square positive
-- statement:
--   The Davies construction uses the one sub adjoint square positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Pinching.lean#L79-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Pinching.lean#L79-L92

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.Davies.one_sub_adjoint_square_positive (A : Operator V) (hA : operatorNorm A ≤ 1) :
    (1 - LinearMap.adjoint A * A).IsPositive := by sorry
