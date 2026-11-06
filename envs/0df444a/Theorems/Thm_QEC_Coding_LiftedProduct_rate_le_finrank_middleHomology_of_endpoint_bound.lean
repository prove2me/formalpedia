-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_rate_le_finrank_middleHomology_of_endpoint_bound
-- name    : QEC.Coding.LiftedProduct.rate_le_finrank_middleHomology_of_endpoint_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:29:55.524604+00:00
-- url     : https://prove2.me/theorems/f4749843-0b38-477a-b09d-e9d129b41f7b
-- title:
--   Lifted Product: rate le finrank middle Homology of endpoint bound
-- statement:
--   Endpoint-cell bounds give the encoded-rate estimate in the PK22 construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L592-L612
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L592-L612

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.rate_le_finrank_middleHomology_of_endpoint_bound
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (rate : ℝ)
    (hEndpoints :
      (Fintype.card (C0Index aRow bRow G) : ℝ) +
        (Fintype.card (C2Index aCol bCol G) : ℝ) ≤
        (1 - rate) * Fintype.card (QubitIndex aRow aCol bRow bCol G)) :
    rate * Fintype.card (QubitIndex aRow aCol bRow bCol G) ≤
      (Module.finrank F (chainComplex D).middleHomology : ℝ) := by sorry
