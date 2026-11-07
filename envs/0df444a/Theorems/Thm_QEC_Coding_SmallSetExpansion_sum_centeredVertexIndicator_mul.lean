-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_centeredVertexIndicator_mul
-- name    : QEC.Coding.SmallSetExpansion.sum_centeredVertexIndicator_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:32:08.110569+00:00
-- url     : https://prove2.me/theorems/e22f2cbe-dff8-411f-b400-f90faa1e70af
-- title:
--   Small Set Expansion: sum centered Vertex Indicator mul
-- statement:
--   Pairing a centered indicator with an arbitrary real function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L121-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L121-L135

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.sum_centeredVertexIndicator_mul
    [Fintype V] [DecidableEq V]
    (S : Finset V) (h : V → ℝ) :
    (∑ v, centeredVertexIndicator S v * h v) =
      Fintype.card V * (∑ v ∈ S, h v) -
        S.card * ∑ v, h v := by sorry
