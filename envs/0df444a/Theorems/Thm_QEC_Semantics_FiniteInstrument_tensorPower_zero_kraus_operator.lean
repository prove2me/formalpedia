-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_zero_kraus_operator
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_zero_kraus_operator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:38:36.407325+00:00
-- url     : https://prove2.me/theorems/ea6b2428-fc15-49d2-8087-ccaa69d9fee9
-- title:
--   Finite Instrument: tensor Power zero kraus operator
-- statement:
--   Depth zero has the literal identity raw branch on the tensor unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L403-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L403-L405

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

theorem QEC.Semantics.FiniteInstrument.tensorPower_zero_kraus_operator (I : FiniteInstrument κ Ω H K) :
    (I.tensorPower 0).kraus.operator PUnit.unit = 1 := by sorry
