-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_complete
-- name    : QEC.Semantics.FiniteInstrument.tensor_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:41:48.624472+00:00
-- url     : https://prove2.me/theorems/147be9b1-64c0-437e-871c-8ecfa00fa092
-- title:
--   Finite Instrument: tensor complete
-- statement:
--   Completeness is preserved by disjoint tensor composition of finite instruments.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L227-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L227-L260

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
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]

theorem QEC.Semantics.FiniteInstrument.tensor_complete (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S)
    (hI : I.kraus.Complete) (hJ : J.kraus.Complete) :
    (I.tensor J).kraus.Complete := by sorry
