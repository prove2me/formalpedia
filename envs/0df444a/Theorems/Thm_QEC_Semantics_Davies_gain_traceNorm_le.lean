-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_gain_traceNorm_le
-- name    : QEC.Semantics.Davies.gain_traceNorm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:27:48.478327+00:00
-- url     : https://prove2.me/theorems/86b4dfcc-25fa-4e5b-848c-b649929a6ff2
-- title:
--   Davies: gain trace Norm le
-- statement:
--   The Davies construction uses the gain trace Norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/TraceBound.lean#L48-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/TraceBound.lean#L48-L63

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

theorem QEC.Semantics.Davies.gain_traceNorm_le (J : κ → Operator V) (F : Operator V)
    (hF : F.IsSymmetric) :
    traceNorm (lindbladJumpGain J F) ≤ operatorNorm (squareSum J) * traceNorm F := by sorry
