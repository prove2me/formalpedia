-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_square
-- name    : QEC.Coding.SmallSetExpansion.crossCount_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:33:24.615205+00:00
-- url     : https://prove2.me/theorems/2c3206b2-6e5a-4c68-bc11-d377d409b390
-- title:
--   Small Set Expansion: cross Count square
-- statement:
--   Cross counts in the square graph group length-two paths by their
--   intermediate vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L483-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L483-L502

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.crossCount_square [Fintype V]
    (M : WeightedGraph V) (S T : Finset V) :
    crossCount (square M) S T =
      ∑ x, incomingCount M S x * outgoingCount M T x := by sorry
