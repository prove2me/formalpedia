-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_weightedJump_squareSum
-- name    : QEC.Semantics.Davies.weightedJump_squareSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:29:15.639592+00:00
-- url     : https://prove2.me/theorems/29f279cb-b832-4026-9990-f3c3059c4f44
-- title:
--   Davies: weighted Jump square Sum
-- statement:
--   The Davies construction uses the weighted Jump square Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/NormBound.lean#L79-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/NormBound.lean#L79-L93

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

theorem QEC.Semantics.Davies.weightedJump_squareSum {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V)
    (rate : κ → Frequency e → ℝ) (hn : ∀ a w, 0 ≤ rate a w) :
    squareSum (weightedJump b e A rate) = ∑ a, rateSquareSum b e (A a) (rate a) := by sorry
