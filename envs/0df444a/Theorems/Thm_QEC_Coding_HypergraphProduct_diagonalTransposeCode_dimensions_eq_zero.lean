-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_diagonalTransposeCode_dimensions_eq_zero
-- name    : QEC.Coding.HypergraphProduct.diagonalTransposeCode_dimensions_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:17:35.982768+00:00
-- url     : https://prove2.me/theorems/57017102-6e69-4279-8f74-70efea5d6291
-- title:
--   Hypergraph Product: diagonal Transpose Code dimensions eq zero
-- statement:
--   The Hypergraph Product construction uses the diagonal Transpose Code dimensions eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L72-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L72-L85

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.diagonalTransposeCode_dimensions_eq_zero
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    Dimension (firstTransposeCode (diagonalData H)) = 0 ∧
      Dimension (secondTransposeCode (diagonalData H)) = 0 := by sorry
