-- Prove2me | Theorems.Thm_QEC_Semantics_continuous_lindbladDysonTermContinuous
-- name    : QEC.Semantics.continuous_lindbladDysonTermContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:24:56.546802+00:00
-- url     : https://prove2.me/theorems/4d47d8b5-60b1-4601-a2d8-914f22e12e4a
-- title:
--   Semantics: continuous lindblad Dyson Term Continuous
-- statement:
--   The Semantics construction uses the continuous lindblad Dyson Term Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L890-L904
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L890-L904

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

theorem QEC.Semantics.continuous_lindbladDysonTermContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H) (n : Nat) :
    Continuous (lindbladDysonTermContinuous K J n) := by sorry
