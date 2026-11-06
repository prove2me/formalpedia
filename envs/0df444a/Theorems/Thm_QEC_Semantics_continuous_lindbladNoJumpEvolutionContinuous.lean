-- Prove2me | Theorems.Thm_QEC_Semantics_continuous_lindbladNoJumpEvolutionContinuous
-- name    : QEC.Semantics.continuous_lindbladNoJumpEvolutionContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:59:06.111879+00:00
-- url     : https://prove2.me/theorems/a45ec6b2-a38c-471b-86f9-7245a3a330a7
-- title:
--   Semantics: continuous lindblad No Jump Evolution Continuous
-- statement:
--   The Semantics construction uses the continuous lindblad No Jump Evolution Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L637-L642
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L637-L642

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

theorem QEC.Semantics.continuous_lindbladNoJumpEvolutionContinuous (K : Operator H) :
    Continuous (lindbladNoJumpEvolutionContinuous K) := by sorry
