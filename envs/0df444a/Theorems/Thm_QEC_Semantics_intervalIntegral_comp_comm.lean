-- Prove2me | Theorems.Thm_QEC_Semantics_intervalIntegral_comp_comm
-- name    : QEC.Semantics.intervalIntegral_comp_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:25:21.988409+00:00
-- url     : https://prove2.me/theorems/a1d17231-9ab7-4324-a629-7fa375666f08
-- title:
--   Semantics: interval Integral comp comm
-- statement:
--   A real continuous-linear map commutes with Bochner interval integration.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L178-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L178-L186

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

theorem QEC.Semantics.intervalIntegral_comp_comm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    (L : E →L[Real] F) (f : Real → E) (a b : Real)
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    (∫ x in a..b, L (f x)) = L (∫ x in a..b, f x) := by sorry
