-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg
-- name    : QEC.Semantics.FiniteInstrument.bornWeight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:24:39.436213+00:00
-- url     : https://prove2.me/theorems/6051f2ff-0e61-474e-b280-4a50d1f9aed3
-- title:
--   Finite Instrument: born Weight nonneg
-- statement:
--   Born weights derived from Kraus branches are nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L91-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L91-L96

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

theorem QEC.Semantics.FiniteInstrument.bornWeight_nonneg (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (rho : DensityOperator H) :
    0 ≤ I.bornWeight outcome rho := by sorry
