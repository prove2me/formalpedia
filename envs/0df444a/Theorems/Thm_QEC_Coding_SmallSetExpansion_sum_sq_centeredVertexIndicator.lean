-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_sq_centeredVertexIndicator
-- name    : QEC.Coding.SmallSetExpansion.sum_sq_centeredVertexIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:32:06.278202+00:00
-- url     : https://prove2.me/theorems/da61182a-5c16-4785-97a9-b556e0f002cb
-- title:
--   Small Set Expansion: sum sq centered Vertex Indicator
-- statement:
--   Squared norm of a division-free centered indicator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L91-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L91-L118

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.sum_sq_centeredVertexIndicator [Fintype V] [DecidableEq V]
    (S : Finset V) :
    ∑ v, (centeredVertexIndicator S v) ^ 2 =
      (Fintype.card V : ℝ) * S.card *
        (Fintype.card V - S.card) := by sorry
