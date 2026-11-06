-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorPower_complete
-- name    : QEC.Semantics.FiniteInstrument.nestedTensorPower_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:31:53.716049+00:00
-- url     : https://prove2.me/theorems/bc98e399-26ac-4eea-b80f-34835916427c
-- title:
--   Finite Instrument: nested Tensor Power complete
-- statement:
--   Completeness is preserved at every nested tensor-power depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/Power.lean#L161-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/Power.lean#L161-L167

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.FiniteInstrument.nestedTensorPower_complete (I : FiniteInstrument kappa Omega H K)
    (hI : I.kraus.Complete) (branches depth : Nat) :
    (nestedTensorPower I branches depth).kraus.Complete := by sorry
