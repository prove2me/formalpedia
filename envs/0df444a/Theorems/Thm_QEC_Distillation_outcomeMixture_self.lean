-- Prove2me | Theorems.Thm_QEC_Distillation_outcomeMixture_self
-- name    : QEC.Distillation.outcomeMixture_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:58:05.953183+00:00
-- url     : https://prove2.me/theorems/6c26f13c-69dd-44ee-9d01-e87bd645a2f9
-- title:
--   Distillation: outcome Mixture self
-- statement:
--   If both conditional branches are the same state, their mixture is that state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L173-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L173-L183

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
set_option autoImplicit false
universe u
open QEC
open QEC.Distillation
open Semantics
open scoped BigOperators

theorem QEC.Distillation.outcomeMixture_self {Output : Type u}
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (successProbability : ℝ) (h0 : 0 ≤ successProbability)
    (h1 : successProbability ≤ 1) (rho : DensityOperator Output) :
    outcomeMixture successProbability h0 h1 rho rho = rho := by sorry
