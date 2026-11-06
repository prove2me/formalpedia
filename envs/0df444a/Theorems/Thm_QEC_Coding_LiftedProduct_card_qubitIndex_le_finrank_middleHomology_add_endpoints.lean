-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_card_qubitIndex_le_finrank_middleHomology_add_endpoints
-- name    : QEC.Coding.LiftedProduct.card_qubitIndex_le_finrank_middleHomology_add_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:53:38.44099+00:00
-- url     : https://prove2.me/theorems/8a887988-b574-4a8f-be2e-bd38cb714fb0
-- title:
--   Lifted Product: card qubit Index le finrank middle Homology add endpoints
-- statement:
--   The lifted-product middle homology loses at most one dimension per endpoint cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L543-L589
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L543-L589

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.card_qubitIndex_le_finrank_middleHomology_add_endpoints
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    Fintype.card (QubitIndex aRow aCol bRow bCol G) ≤
      Module.finrank F (chainComplex D).middleHomology +
        Fintype.card (C0Index aRow bRow G) +
        Fintype.card (C2Index aCol bCol G) := by sorry
