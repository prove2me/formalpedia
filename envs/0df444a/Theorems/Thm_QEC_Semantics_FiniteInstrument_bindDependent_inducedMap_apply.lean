-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_inducedMap_apply
-- name    : QEC.Semantics.FiniteInstrument.bindDependent_inducedMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:19:07.461201+00:00
-- url     : https://prove2.me/theorems/fb3f359e-7799-4ada-b238-ecf75e190f3d
-- title:
--   Finite Instrument: bind Dependent induced Map apply
-- statement:
--   The induced map decomposes over the actual dependent raw-index fibres.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/DependentComposition.lean#L66-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/DependentComposition.lean#L66-L77

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

theorem QEC.Semantics.FiniteInstrument.bindDependent_inducedMap_apply (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L)
    (A : Operator H) :
    (I.bindDependent J).kraus.inducedMap A =
      ∑ firstIndex : κ,
        (J (I.observe firstIndex)).kraus.inducedMap
          ((I.kraus.operator firstIndex).comp
            (A.comp (LinearMap.adjoint (I.kraus.operator firstIndex)))) := by sorry
