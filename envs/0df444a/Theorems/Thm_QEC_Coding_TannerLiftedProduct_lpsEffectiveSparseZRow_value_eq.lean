-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveSparseZRow_value_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveSparseZRow_value_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:13:32.435717+00:00
-- url     : https://prove2.me/theorems/1a6d4cac-3e57-4ff7-9d86-5cfc74224fd8
-- title:
--   Tanner Lifted Product: lps Effective Sparse ZRow value eq
-- statement:
--   The Tanner Lifted Product construction uses the lps Effective Sparse ZRow value eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L480-L492
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L480-L492

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveSparseZRow_value_eq {p D r r' : ℕ} {F : Type} [Field F] [Fintype F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (z : LPSSparseZIndex (lpsEffectiveResiduePrimeAt hp hp4 n).q D r')
    (qubit : LPSSparseQubitIndex (lpsEffectiveResiduePrimeAt hp hp4 n).q D r r') :
    lpsSparseRowValue (lpsEffectiveSparseZRow hp hp4 n generators h h' z) qubit =
      LiftedProduct.boundary2Matrix
        (data (fun j => lpsEffectiveQuaternionFamilyLabel hp hp4 n (generators j)) h h')
        (lpsSparseQubitDecode qubit) (lpsSparseZDecode z) := by sorry
