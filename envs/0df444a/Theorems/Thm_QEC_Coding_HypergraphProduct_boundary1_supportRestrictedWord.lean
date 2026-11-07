-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_boundary1_supportRestrictedWord
-- name    : QEC.Coding.HypergraphProduct.boundary1_supportRestrictedWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:38:02.606082+00:00
-- url     : https://prove2.me/theorems/12ba0d2e-ad44-46d0-b614-3c688f9aee50
-- title:
--   Hypergraph Product: boundary1 support Restricted Word
-- statement:
--   Restricting to the two support projections preserves the first boundary
--   of the supported word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L55-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L55-L87

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.boundary1_supportRestrictedWord
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo)) :
    boundary1 (supportRestrictedData D z) (supportRestrictedWord z) =
      boundary1 D z := by sorry
