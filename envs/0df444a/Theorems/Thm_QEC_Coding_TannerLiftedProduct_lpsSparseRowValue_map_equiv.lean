-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseRowValue_map_equiv
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseRowValue_map_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:11:25.557641+00:00
-- url     : https://prove2.me/theorems/3cc9bd77-1e4c-47ea-8e70-e6e6d207ad70
-- title:
--   Tanner Lifted Product: lps Sparse Row Value map equiv
-- statement:
--   The Tanner Lifted Product construction uses the lps Sparse Row Value map equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L344-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L344-L348

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseRowValue_map_equiv {Q Q' F : Type} [DecidableEq Q] [DecidableEq Q']
    [AddCommMonoid F] (e : Q ≃ Q') (row : List (Q × F)) (x : Q) :
    lpsSparseRowValue (row.map fun entry => (e entry.1, entry.2)) (e x) =
      lpsSparseRowValue row x := by sorry
