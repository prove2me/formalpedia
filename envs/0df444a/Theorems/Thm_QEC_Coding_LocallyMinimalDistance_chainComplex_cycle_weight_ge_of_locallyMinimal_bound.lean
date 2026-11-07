-- Prove2me | Theorems.Thm_QEC_Coding_LocallyMinimalDistance_chainComplex_cycle_weight_ge_of_locallyMinimal_bound
-- name    : QEC.Coding.LocallyMinimalDistance.chainComplex_cycle_weight_ge_of_locallyMinimal_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:56.719679+00:00
-- url     : https://prove2.me/theorems/995ceafd-7779-4510-8e35-44cfbd34a876
-- title:
--   Locally Minimal Distance: chain Complex cycle weight ge of locally Minimal bound
-- statement:
--   Local minimal-cycle expansion bounds the weight of every non-boundary cycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L117-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L117-L134

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]

theorem QEC.Coding.LocallyMinimalDistance.chainComplex_cycle_weight_ge_of_locallyMinimal_bound
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (weight : Word F ι → Nat)
    (lowerBound : Nat)
    (hlocal : ∀ c : Word F ι, c ∈ K.middleCycleCode.carrier → c ≠ 0 →
      IsLocallyMinimal weight (elementaryBoundaryMoves K) c →
        lowerBound ≤ weight c)
    (c : Word F ι) (hcZ : c ∈ K.middleCycleCode.carrier)
    (hcB : c ∉ K.middleBoundaryCode.carrier) :
    lowerBound ≤ weight c := by sorry
