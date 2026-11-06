-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_complete
-- name    : QEC.Semantics.FiniteInstrument.bindDependent_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:47:47.458684+00:00
-- url     : https://prove2.me/theorems/b401bd8f-9a46-43da-a33a-b051d215ec53
-- title:
--   Finite Instrument: bind Dependent complete
-- statement:
--   Completeness is preserved by dependent finite sequential binding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/DependentComposition.lean#L80-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/DependentComposition.lean#L80-L106

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

theorem QEC.Semantics.FiniteInstrument.bindDependent_complete (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L)
    (hI : I.kraus.Complete)
    (hJ : ∀ outcome, (J outcome).kraus.Complete) :
    (I.bindDependent J).kraus.Complete := by sorry
