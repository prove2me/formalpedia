-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_trace_re
-- name    : QEC.Semantics.FiniteInstrument.sum_bornWeight_eq_trace_re
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:18:28.860194+00:00
-- url     : https://prove2.me/theorems/ba2149b4-cc18-4f08-b214-e99813f3d5ea
-- title:
--   Finite Instrument: sum born Weight eq trace re
-- statement:
--   For a complete Kraus family, observable Born weights sum to the real part of
--   the input trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L113-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L113-L119

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Instruments_Core
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
attribute [local instance] QEC.Semantics.FiniteInstrument._p2m_local_instance_a5f1a79248_39

theorem QEC.Semantics.FiniteInstrument.sum_bornWeight_eq_trace_re (I : FiniteInstrument κ Ω H K)
    (hComplete : I.kraus.Complete) (rho : DensityOperator H) :
    ∑ outcome : Ω, I.bornWeight outcome rho =
      Complex.re (LinearMap.trace Complex H rho.toOperator) := by sorry
