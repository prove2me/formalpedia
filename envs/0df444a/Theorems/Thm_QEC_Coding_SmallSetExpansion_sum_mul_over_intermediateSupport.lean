-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_mul_over_intermediateSupport
-- name    : QEC.Coding.SmallSetExpansion.sum_mul_over_intermediateSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:37:25.924358+00:00
-- url     : https://prove2.me/theorems/d4978b90-da31-4653-8e48-c81197b4289e
-- title:
--   Small Set Expansion: sum mul over intermediate Support
-- statement:
--   Terms outside the intermediate support vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L571-L582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L571-L582

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.sum_mul_over_intermediateSupport
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (S T : Finset V) :
    (∑ x, incomingCount M S x * outgoingCount M T x) =
      ∑ x ∈ intermediateSupport M S,
        incomingCount M S x * outgoingCount M T x := by sorry
