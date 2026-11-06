-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_eq_zero_of_bornWeight_eq_zero
-- name    : QEC.Semantics.FiniteInstrument.branchOperator_eq_zero_of_bornWeight_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:18:36.614134+00:00
-- url     : https://prove2.me/theorems/79ea0b26-b8ac-4b34-9deb-099778444728
-- title:
--   Finite Instrument: branch Operator eq zero of born Weight eq zero
-- statement:
--   A zero Born weight forces the corresponding positive raw branch to vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L154-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L154-L161

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

theorem QEC.Semantics.FiniteInstrument.branchOperator_eq_zero_of_bornWeight_eq_zero
    (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (rho : DensityOperator H) (hzero : I.bornWeight outcome rho = 0) :
    I.branchOperator outcome rho.toOperator = 0 := by sorry
