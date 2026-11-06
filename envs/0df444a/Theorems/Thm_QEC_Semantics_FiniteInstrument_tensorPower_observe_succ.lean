-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_observe_succ
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_observe_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:39:20.795206+00:00
-- url     : https://prove2.me/theorems/fa894ed3-7a45-4f60-9d7c-20a088f8ddd6
-- title:
--   Finite Instrument: tensor Power observe succ
-- statement:
--   A successor observation keeps the supplied head outcome and its history tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L416-L420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L416-L420

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

theorem QEC.Semantics.FiniteInstrument.tensorPower_observe_succ (I : FiniteInstrument κ Ω H K)
    (n : Nat) (head : κ) (tail : tensorPowerHistory κ n) :
    (I.tensorPower (n + 1)).observe (head, tail) =
      (I.observe head, (I.tensorPower n).observe tail) := by sorry
