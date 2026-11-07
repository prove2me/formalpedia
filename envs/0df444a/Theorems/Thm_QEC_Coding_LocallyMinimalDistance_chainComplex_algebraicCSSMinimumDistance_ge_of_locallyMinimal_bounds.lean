-- Prove2me | Theorems.Thm_QEC_Coding_LocallyMinimalDistance_chainComplex_algebraicCSSMinimumDistance_ge_of_locallyMinimal_bounds
-- name    : QEC.Coding.LocallyMinimalDistance.chainComplex_algebraicCSSMinimumDistance_ge_of_locallyMinimal_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:54:39.492034+00:00
-- url     : https://prove2.me/theorems/f22db0be-28ed-4bda-bd27-49776e68e8ff
-- title:
--   Locally Minimal Distance: chain Complex algebraic CSSMinimum Distance ge of locally Minimal bounds
-- statement:
--   Primal and dual locally minimal expansion bound algebraic CSS distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L180-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L180-L207

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]

theorem QEC.Coding.LocallyMinimalDistance.chainComplex_algebraicCSSMinimumDistance_ge_of_locallyMinimal_bounds
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (weight : Word F ι → Nat) (lowerBound d : Nat)
    (hweight : ∀ c : Word F ι, weight c ≤ HammingWeight c)
    (hcycles : ∀ c : Word F ι, c ∈ K.middleCycleCode.carrier → c ≠ 0 →
      IsLocallyMinimal weight (elementaryBoundaryMoves K) c →
        lowerBound ≤ weight c)
    (hcocycles : ∀ c : Word F ι, c ∈ K.middleCocycleCode.carrier → c ≠ 0 →
      IsLocallyMinimal weight (elementaryCoboundaryMoves K) c →
        lowerBound ≤ weight c)
    (hminimum : AlgebraicCSSMinimumDistance
      K.firstCoboundaryCheckCode K.middleBoundaryCode d) :
    lowerBound ≤ d := by sorry
