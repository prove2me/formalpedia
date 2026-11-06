-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_boundaryIncidence_boundedLocality_of_bounds
-- name    : QEC.Coding.LiftedProduct.boundaryIncidence_boundedLocality_of_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:30:32.899022+00:00
-- url     : https://prove2.me/theorems/c398d839-ee32-43c3-b1fb-3437d4beb37e
-- title:
--   Lifted Product: boundary Incidence bounded Locality of bounds
-- statement:
--   Explicit row and column bounds imply bounded locality for the constructed incidence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L895-L912
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L895-L912

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.boundaryIncidence_boundedLocality_of_bounds
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) {B : Nat}
    (hrow1 : ∀ c0, (boundary1RowSupport D c0).card ≤ B)
    (hrow2 : ∀ c2, (boundary2RowSupport D c2).card ≤ B)
    (hcol : ∀ q, ((boundaryIncidence D).variableSupport q).card ≤ B) :
    QEC.Coding.BoundedLocality (boundaryIncidence D).localityProfile B := by sorry
