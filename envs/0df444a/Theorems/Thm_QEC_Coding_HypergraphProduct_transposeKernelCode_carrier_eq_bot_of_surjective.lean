-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_transposeKernelCode_carrier_eq_bot_of_surjective
-- name    : QEC.Coding.HypergraphProduct.transposeKernelCode_carrier_eq_bot_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:21:03.199779+00:00
-- url     : https://prove2.me/theorems/54092b91-f296-4de3-9d3b-28f02c51533e
-- title:
--   Hypergraph Product: transpose Kernel Code carrier eq bot of surjective
-- statement:
--   A full-row-rank parity-check matrix has zero transpose code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L49-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L49-L59

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.transposeKernelCode_carrier_eq_bot_of_surjective
    {F : Type v} {Row Col : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col F) (hFull : Function.Surjective (Matrix.toLin' H)) :
    (parityCheckKernelCode (Matrix.toLin' H.transpose)).carrier = ⊥ := by sorry
