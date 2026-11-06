-- Prove2me | Theorems.Thm_QEC_Locality_separatorLeftEdges_reverse
-- name    : QEC.Locality.separatorLeftEdges_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:22.328931+00:00
-- url     : https://prove2.me/theorems/0a3cc3d4-b441-4fcf-914d-66b719fe1133
-- title:
--   Locality: separator Left Edges reverse
-- statement:
--   A reverse-symmetric node edge set stays reverse-symmetric after separator allocation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Quantitative.lean#L25-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Quantitative.lean#L25-L34

import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
set_option autoImplicit false
open QEC QEC.Locality
universe u

theorem QEC.Locality.separatorLeftEdges_reverse {ι : Type u} [DecidableEq ι]
    (edges : Finset (ι × ι)) (left : Finset ι)
    (hsymmetric : ∀ x y, (x, y) ∈ edges ↔ (y, x) ∈ edges) (x y : ι) :
    (x, y) ∈ separatorLeftEdges edges left ↔ (y, x) ∈ separatorLeftEdges edges left := by sorry
