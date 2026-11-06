-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_one_sub_frequency_squareSum_positive
-- name    : QEC.Semantics.Davies.one_sub_frequency_squareSum_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:28:27.58726+00:00
-- url     : https://prove2.me/theorems/863fbe21-f61c-4cb0-b9ed-47ba3826071b
-- title:
--   Davies: one sub frequency square Sum positive
-- statement:
--   The Davies construction uses the one sub frequency square Sum positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Pinching.lean#L94-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Pinching.lean#L94-L99

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

theorem QEC.Semantics.Davies.one_sub_frequency_squareSum_positive (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : Operator V) (hA : operatorNorm A ≤ 1) :
    (1 - squareSum (fun ω : Frequency e => frequencyComponent b e A ω.val)).IsPositive := by sorry
