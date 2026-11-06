-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one
-- name    : QEC.Semantics.FiniteInstrument.sum_bornWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:23:41.77429+00:00
-- url     : https://prove2.me/theorems/a7621d80-c6af-4572-b38c-06dd692fba52
-- title:
--   Finite Instrument: sum born Weight eq one
-- statement:
--   Observable Born weights of a complete instrument sum to one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L122-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L122-L126

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

theorem QEC.Semantics.FiniteInstrument.sum_bornWeight_eq_one (I : FiniteInstrument κ Ω H K)
    (hComplete : I.kraus.Complete) (rho : DensityOperator H) :
    ∑ outcome : Ω, I.bornWeight outcome rho = 1 := by sorry
