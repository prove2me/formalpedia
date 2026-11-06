-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_mapDensity_toOperator
-- name    : QEC.Semantics.FiniteInstrument.sum_branchOperator_eq_mapDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:33:15.502196+00:00
-- url     : https://prove2.me/theorems/fb80d293-b404-4f7b-82f3-19296cf845da
-- title:
--   Finite Instrument: sum branch Operator eq map Density to Operator
-- statement:
--   Observable raw branches reconstruct the complete channel output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L129-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean#L129-L135

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

theorem QEC.Semantics.FiniteInstrument.sum_branchOperator_eq_mapDensity_toOperator
    (I : FiniteInstrument κ Ω H K) (hComplete : I.kraus.Complete)
    (rho : DensityOperator H) :
    ∑ outcome : Ω, I.branchOperator outcome rho.toOperator =
      ((I.kraus.toQuantumChannel hComplete).mapDensity rho).toOperator := by sorry
