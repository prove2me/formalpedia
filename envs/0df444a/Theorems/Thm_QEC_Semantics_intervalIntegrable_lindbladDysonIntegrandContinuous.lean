-- Prove2me | Theorems.Thm_QEC_Semantics_intervalIntegrable_lindbladDysonIntegrandContinuous
-- name    : QEC.Semantics.intervalIntegrable_lindbladDysonIntegrandContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:25:11.817024+00:00
-- url     : https://prove2.me/theorems/47f8611a-f9c4-412f-ae42-ea9f7c62f374
-- title:
--   Semantics: interval Integrable lindblad Dyson Integrand Continuous
-- statement:
--   The Semantics construction uses the interval Integrable lindblad Dyson Integrand Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L906-L914
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L906-L914

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

theorem QEC.Semantics.intervalIntegrable_lindbladDysonIntegrandContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H) (n : Nat) (t : Real) :
    IntervalIntegrable
      (lindbladDysonIntegrandContinuous K J
        (lindbladDysonTermContinuous K J n) t)
      MeasureTheory.volume 0 t := by sorry
