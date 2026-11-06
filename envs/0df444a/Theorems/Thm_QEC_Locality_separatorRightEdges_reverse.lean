-- Prove2me | Theorems.Thm_QEC_Locality_separatorRightEdges_reverse
-- name    : QEC.Locality.separatorRightEdges_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:16.75783+00:00
-- url     : https://prove2.me/theorems/4e4ab233-451b-4919-bf64-2f592d94e6c3
-- title:
--   Locality: separator Right Edges reverse
-- statement:
--   The Locality construction uses the separator Right Edges reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Quantitative.lean#L36-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Quantitative.lean#L36-L45

import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
set_option autoImplicit false
open QEC QEC.Locality
universe u

theorem QEC.Locality.separatorRightEdges_reverse {ι : Type u} [DecidableEq ι]
    (edges : Finset (ι × ι)) (left : Finset ι)
    (hsymmetric : ∀ x y, (x, y) ∈ edges ↔ (y, x) ∈ edges) (x y : ι) :
    (x, y) ∈ separatorRightEdges edges left ↔ (y, x) ∈ separatorRightEdges edges left := by sorry
