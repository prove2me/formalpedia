-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_weightedJump_dissipatorNorm_le
-- name    : QEC.Semantics.Davies.weightedJump_dissipatorNorm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:29:05.54318+00:00
-- url     : https://prove2.me/theorems/0c9ca072-c7e1-4c45-a3a0-9add1a562987
-- title:
--   Davies: weighted Jump dissipator Norm le
-- statement:
--   CLBT's self-adjoint induced norm counts physical couplings only.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/NormBound.lean#L111-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/NormBound.lean#L111-L118

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

theorem QEC.Semantics.Davies.weightedJump_dissipatorNorm_le [Nontrivial V] {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V)
    (hA : ∀ a, operatorNorm (A a) ≤ 1) (rate : κ → Frequency e → ℝ)
    (hmax : ℝ) (hm : 0 ≤ hmax) (hn : ∀ a w, 0 ≤ rate a w) (hu : ∀ a w, rate a w ≤ hmax) :
    lindbladDissipatorNorm (weightedJump b e A rate) ≤ 2 * Fintype.card κ * hmax := by sorry
