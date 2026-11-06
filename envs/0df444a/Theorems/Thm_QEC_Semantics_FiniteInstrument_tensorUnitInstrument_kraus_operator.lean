-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorUnitInstrument_kraus_operator
-- name    : QEC.Semantics.FiniteInstrument.tensorUnitInstrument_kraus_operator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:38:24.405123+00:00
-- url     : https://prove2.me/theorems/a2430fc8-d2b6-476a-932a-493772ec6dbe
-- title:
--   Finite Instrument: tensor Unit Instrument kraus operator
-- statement:
--   The Finite Instrument construction uses the tensor Unit Instrument kraus operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L382-L384
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L382-L384

import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ' : Type x} [Fintype κ']
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.tensorUnitInstrument_kraus_operator :
    tensorUnitInstrument.kraus.operator PUnit.unit = 1 := by sorry
