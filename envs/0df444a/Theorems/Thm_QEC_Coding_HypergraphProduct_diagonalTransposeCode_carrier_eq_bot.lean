-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_diagonalTransposeCode_carrier_eq_bot
-- name    : QEC.Coding.HypergraphProduct.diagonalTransposeCode_carrier_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:16:50.402427+00:00
-- url     : https://prove2.me/theorems/d7f1a0e7-3b50-49e8-b641-716227b78970
-- title:
--   Hypergraph Product: diagonal Transpose Code carrier eq bot
-- statement:
--   The Hypergraph Product construction uses the diagonal Transpose Code carrier eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L61-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L61-L70

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.diagonalTransposeCode_carrier_eq_bot
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    (firstTransposeCode (diagonalData H)).carrier = ⊥ ∧
      (secondTransposeCode (diagonalData H)).carrier = ⊥ := by sorry
