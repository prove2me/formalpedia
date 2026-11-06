-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_kraus_operator
-- name    : QEC.Semantics.FiniteInstrument.bindDependent_kraus_operator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:47:40.289475+00:00
-- url     : https://prove2.me/theorems/790b3fc7-1905-46d4-b1a9-570513c3e50e
-- title:
--   Finite Instrument: bind Dependent kraus operator
-- statement:
--   A dependent composite raw branch is the selected second branch after its first branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/DependentComposition.lean#L49-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/DependentComposition.lean#L49-L55

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

theorem QEC.Semantics.FiniteInstrument.bindDependent_kraus_operator (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L)
    (firstIndex : κ) (secondIndex : κ₂ (I.observe firstIndex)) :
    (I.bindDependent J).kraus.operator ⟨firstIndex, secondIndex⟩ =
      ((J (I.observe firstIndex)).kraus.operator secondIndex).comp
        (I.kraus.operator firstIndex) := by sorry
