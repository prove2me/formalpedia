-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_ker_restrictColumns_eq_bot_of_card_lt_extendedMinimumDistance
-- name    : QEC.Coding.HypergraphProduct.ker_restrictColumns_eq_bot_of_card_lt_extendedMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:28:06.886512+00:00
-- url     : https://prove2.me/theorems/02b52f44-aa1c-4010-88c8-54f883316679
-- title:
--   Hypergraph Product: ker restrict Columns eq bot of card lt extended Minimum Distance
-- statement:
--   If fewer columns are retained than the source-convention distance, the
--   column-restricted parity-check matrix has trivial kernel.  This includes the
--   case of an original zero code, whose extended distance is infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Support.lean#L122-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Support.lean#L122-L152

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Support
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.ker_restrictColumns_eq_bot_of_card_lt_extendedMinimumDistance
    {F : Type v} {Row I : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Row] [DecidableEq Row]
    [Fintype I] [DecidableEq I]
    (H : Matrix Row I F) (A : Finset I)
    (hA : (A.card : WithTop Nat) <
      extendedMinimumDistance
        (parityCheckKernelCode (Matrix.toLin' H))) :
    LinearMap.ker (Matrix.toLin' (restrictColumns H A)) = ⊥ := by sorry
