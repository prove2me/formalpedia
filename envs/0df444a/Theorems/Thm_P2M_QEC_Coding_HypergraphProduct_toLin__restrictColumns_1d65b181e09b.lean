-- Prove2me | Theorems.Thm_P2M_QEC_Coding_HypergraphProduct_toLin__restrictColumns_1d65b181e09b
-- name    : P2M_QEC_Coding_HypergraphProduct_toLin__restrictColumns_1d65b181e09b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:37:42.227537+00:00
-- url     : https://prove2.me/theorems/ad14c182-9c6b-46c0-93c8-9862a2a417b0
-- title:
--   P2 M QEC Coding Hypergraph Product to Lin  restrict Columns 1d65b181e09b: P2 M QEC Coding Hypergraph Product to Lin  restrict Columns 1d65b181e09b
-- statement:
--   Multiplication by a column-restricted matrix is multiplication by the
--   original matrix after zero extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Support.lean#L80-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Support.lean#L80-L102

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Support
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem P2M_QEC_Coding_HypergraphProduct_toLin__restrictColumns_1d65b181e09b
    {F : Type v} {Row I : Type u}
    [Field F]
    [Fintype Row] [Fintype I] [DecidableEq I]
    (H : Matrix Row I F) (A : Finset I) (x : Word F {i // i ∈ A}) :
    Matrix.toLin' (restrictColumns H A) x =
      Matrix.toLin' H (zeroExtend A x) := by sorry

alias «QEC».«Coding».«HypergraphProduct».«toLin'_restrictColumns» := P2M_QEC_Coding_HypergraphProduct_toLin__restrictColumns_1d65b181e09b
