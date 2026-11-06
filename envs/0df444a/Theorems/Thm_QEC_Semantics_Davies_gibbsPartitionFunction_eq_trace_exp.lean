-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_gibbsPartitionFunction_eq_trace_exp
-- name    : QEC.Semantics.Davies.gibbsPartitionFunction_eq_trace_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:28:47.426202+00:00
-- url     : https://prove2.me/theorems/3797ddae-f86d-49b9-be8c-6ebf04c2a48d
-- title:
--   Davies: gibbs Partition Function eq trace exp
-- statement:
--   The Davies construction uses the gibbs Partition Function eq trace exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L227-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L227-L237

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem QEC.Semantics.Davies.gibbsPartitionFunction_eq_trace_exp (H : Operator V)
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (heigen : ∀ i, H (b i) = (e i : ℂ) • b i) (β : ℝ) :
    (gibbsPartitionFunction β e : ℂ) = LinearMap.trace ℂ V
      (NormedSpace.exp ((-β : ℂ) • LinearMap.toContinuousLinearMap H)).toLinearMap := by sorry
