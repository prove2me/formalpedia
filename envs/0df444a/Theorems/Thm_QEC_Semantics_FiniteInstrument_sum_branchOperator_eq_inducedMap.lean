-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_inducedMap
-- name    : QEC.Semantics.FiniteInstrument.sum_branchOperator_eq_inducedMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:24:38.996212+00:00
-- url     : https://prove2.me/theorems/fe9569eb-893f-4e91-88f4-bd4c1b9e8534
-- title:
--   Finite Instrument: sum branch Operator eq induced Map
-- statement:
--   Summing all observable branches recovers the raw Kraus operator sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L99-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L99-L107

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

theorem QEC.Semantics.FiniteInstrument.sum_branchOperator_eq_inducedMap (I : FiniteInstrument κ Ω H K)
    (A : Operator H) :
    ∑ outcome : Ω, I.branchOperator outcome A =
      I.kraus.inducedMap A := by sorry
