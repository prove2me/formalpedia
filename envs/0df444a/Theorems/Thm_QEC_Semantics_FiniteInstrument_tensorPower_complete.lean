-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:40:24.641341+00:00
-- url     : https://prove2.me/theorems/3a861c7b-7a6e-43d1-9335-8154d52809cd
-- title:
--   Finite Instrument: tensor Power complete
-- statement:
--   Completeness follows by recursion from unit identity and binary tensor completeness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L423-L428
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L423-L428

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

theorem QEC.Semantics.FiniteInstrument.tensorPower_complete (I : FiniteInstrument κ Ω H K)
    (hI : I.kraus.Complete) (n : Nat) :
    (I.tensorPower n).kraus.Complete := by sorry
