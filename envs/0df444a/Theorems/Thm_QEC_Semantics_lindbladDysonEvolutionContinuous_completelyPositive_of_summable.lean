-- Prove2me | Theorems.Thm_QEC_Semantics_lindbladDysonEvolutionContinuous_completelyPositive_of_summable
-- name    : QEC.Semantics.lindbladDysonEvolutionContinuous_completelyPositive_of_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:03:09.668226+00:00
-- url     : https://prove2.me/theorems/35139da5-f7a0-4f71-93b6-2185f746e575
-- title:
--   Semantics: lindblad Dyson Evolution Continuous completely Positive of summable
-- statement:
--   The Semantics construction uses the lindblad Dyson Evolution Continuous completely Positive of summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L1225-L1233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L1225-L1233

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
attribute [local instance] QEC.Semantics.finiteQuantumSystemComplete

theorem QEC.Semantics.lindbladDysonEvolutionContinuous_completelyPositive_of_summable
    [Fintype ι] (K : Operator H) (J : ι → Operator H)
    (t : Real) (ht : 0 ≤ t)
    (hsummable : Summable (fun n => lindbladDysonTermContinuous K J n t)) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladDysonEvolutionContinuous K J t)) := by sorry
