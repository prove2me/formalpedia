-- Prove2me | Theorems.Thm_QEC_Coding_LocallyMinimalDistance_chainComplex_cocycle_weight_ge_of_locallyMinimal_bound
-- name    : QEC.Coding.LocallyMinimalDistance.chainComplex_cocycle_weight_ge_of_locallyMinimal_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:56.996327+00:00
-- url     : https://prove2.me/theorems/c2d1f97c-7f29-450b-be91-2003415ddcd3
-- title:
--   Locally Minimal Distance: chain Complex cocycle weight ge of locally Minimal bound
-- statement:
--   The dual local-minimal bound controls every non-coboundary cocycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L160-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L160-L177

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]

theorem QEC.Coding.LocallyMinimalDistance.chainComplex_cocycle_weight_ge_of_locallyMinimal_bound
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (weight : Word F ι → Nat) (lowerBound : Nat)
    (hlocal : ∀ c : Word F ι, c ∈ K.middleCocycleCode.carrier → c ≠ 0 →
      IsLocallyMinimal weight (elementaryCoboundaryMoves K) c →
        lowerBound ≤ weight c)
    (c : Word F ι) (hcZ : c ∈ K.middleCocycleCode.carrier)
    (hcB : c ∉ K.firstCoboundaryCheckCode.carrier) :
    lowerBound ≤ weight c := by sorry
