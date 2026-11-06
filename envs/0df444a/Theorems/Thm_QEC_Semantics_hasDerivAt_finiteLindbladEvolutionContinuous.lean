-- Prove2me | Theorems.Thm_QEC_Semantics_hasDerivAt_finiteLindbladEvolutionContinuous
-- name    : QEC.Semantics.hasDerivAt_finiteLindbladEvolutionContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:25:20.048321+00:00
-- url     : https://prove2.me/theorems/20eb25c1-f8f7-4ecb-bf0e-eef9d4f29ca7
-- title:
--   Semantics: has Deriv At finite Lindblad Evolution Continuous
-- statement:
--   The Semantics construction uses the has Deriv At finite Lindblad Evolution Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L1332-L1338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L1332-L1338

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

theorem QEC.Semantics.hasDerivAt_finiteLindbladEvolutionContinuous [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (z : Complex) :
    HasDerivAt (finiteLindbladEvolutionContinuous hamiltonian J)
      (finiteLindbladEvolutionContinuous hamiltonian J z *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) z := by sorry
