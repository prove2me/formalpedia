-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_branchOperator
-- name    : QEC.Semantics.FiniteInstrument.bind_branchOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:18:45.024382+00:00
-- url     : https://prove2.me/theorems/3b909420-41db-46ad-91f2-2c56c0dd4357
-- title:
--   Finite Instrument: bind branch Operator
-- statement:
--   A retained composite observation is exactly the selected second branch
--   applied to the retained first branch.  The predecessor branch remains
--   unnormalized, so this identity introduces no conditional-state division.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L59-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L59-L107

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

theorem QEC.Semantics.FiniteInstrument.bind_branchOperator (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument κ' (Ξ outcome) K L)
    (firstOutcome : Ω) (secondOutcome : Ξ firstOutcome) (A : Operator H) :
    (I.bind J).branchOperator ⟨firstOutcome, secondOutcome⟩ A =
      (J firstOutcome).branchOperator secondOutcome
        (I.branchOperator firstOutcome A) := by sorry
