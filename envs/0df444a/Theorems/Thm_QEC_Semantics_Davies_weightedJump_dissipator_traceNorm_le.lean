-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_weightedJump_dissipator_traceNorm_le
-- name    : QEC.Semantics.Davies.weightedJump_dissipator_traceNorm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:10:48.515206+00:00
-- url     : https://prove2.me/theorems/83872f4b-2e32-40dc-b22d-ea13adbd2eeb
-- title:
--   Davies: weighted Jump dissipator trace Norm le
-- statement:
--   Pointwise source norm estimate on every self-adjoint input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/NormBound.lean#L121-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/NormBound.lean#L121-L132

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators ComplexOrder
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.Davies.weightedJump_dissipator_traceNorm_le [Nontrivial V] {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V)
    (hA : ∀ a, operatorNorm (A a) ≤ 1) (rate : κ → Frequency e → ℝ)
    (hmax : ℝ) (hm : 0 ≤ hmax) (hn : ∀ a w, 0 ≤ rate a w) (hu : ∀ a w, rate a w ≤ hmax)
    (F : Operator V) (hF : F.IsSymmetric) :
    traceNorm (lindbladDissipator (weightedJump b e A rate) F) ≤
      (2 * Fintype.card κ * hmax) * traceNorm F := by sorry
