-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_dimension_kernelCode_add_rank
-- name    : QEC.Coding.HypergraphProduct.dimension_kernelCode_add_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:52:22.950787+00:00
-- url     : https://prove2.me/theorems/0d027f39-ec0d-404b-865f-f65dd463ef3c
-- title:
--   Hypergraph Product: dimension kernel Code add rank
-- statement:
--   Rank-nullity for a parity-check matrix, stated as code dimension plus
--   matrix rank equals the number of columns.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Parameters.lean#L100-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Parameters.lean#L100-L113

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.dimension_kernelCode_add_rank
    {F : Type v} {row col : Type u}
    [Field F] [Fintype F]
    [Fintype row] [DecidableEq row]
    [Fintype col] [DecidableEq col]
    (H : Matrix row col F) :
    Dimension (parityCheckKernelCode (Matrix.toLin' H)) + H.rank =
      Fintype.card col := by sorry
