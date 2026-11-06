-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_kraus_operator
-- name    : QEC.Semantics.FiniteInstrument.bind_kraus_operator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:18:48.842265+00:00
-- url     : https://prove2.me/theorems/891dac18-759e-4d4b-967c-a2cba6fc24a6
-- title:
--   Finite Instrument: bind kraus operator
-- statement:
--   A composite raw Kraus branch is the selected second branch after the first.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L48-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L48-L54

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

theorem QEC.Semantics.FiniteInstrument.bind_kraus_operator (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument κ' (Ξ outcome) K L)
    (firstIndex : κ) (secondIndex : κ') :
    (I.bind J).kraus.operator (firstIndex, secondIndex) =
      ((J (I.observe firstIndex)).kraus.operator secondIndex).comp
        (I.kraus.operator firstIndex) := by sorry
