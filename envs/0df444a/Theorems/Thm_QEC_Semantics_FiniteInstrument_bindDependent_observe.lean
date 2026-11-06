-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_observe
-- name    : QEC.Semantics.FiniteInstrument.bindDependent_observe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:44:36.769833+00:00
-- url     : https://prove2.me/theorems/81ffebae-4c35-45f9-b4c2-c4237e90a9b9
-- title:
--   Finite Instrument: bind Dependent observe
-- statement:
--   A dependent composite observation records both actual stage observations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/DependentComposition.lean#L58-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/DependentComposition.lean#L58-L63

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ₂ : Ω → Type x} [∀ outcome, Fintype (κ₂ outcome)]
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.bindDependent_observe (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L)
    (firstIndex : κ) (secondIndex : κ₂ (I.observe firstIndex)) :
    (I.bindDependent J).observe ⟨firstIndex, secondIndex⟩ =
      ⟨I.observe firstIndex, (J (I.observe firstIndex)).observe secondIndex⟩ := by sorry
