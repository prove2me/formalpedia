-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveSparseXRow_value_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveSparseXRow_value_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:13:39.103691+00:00
-- url     : https://prove2.me/theorems/861e4f79-0ab4-45bb-aa06-dad95ec71453
-- title:
--   Tanner Lifted Product: lps Effective Sparse XRow value eq
-- statement:
--   The Tanner Lifted Product construction uses the lps Effective Sparse XRow value eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L466-L478
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L466-L478

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveSparseXRow_value_eq {p D r r' : ℕ} {F : Type} [Field F] [Fintype F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (x : LPSSparseXIndex (lpsEffectiveResiduePrimeAt hp hp4 n).q D r)
    (qubit : LPSSparseQubitIndex (lpsEffectiveResiduePrimeAt hp hp4 n).q D r r') :
    lpsSparseRowValue (lpsEffectiveSparseXRow hp hp4 n generators h h' x) qubit =
      LiftedProduct.boundary1Matrix
        (data (fun j => lpsEffectiveQuaternionFamilyLabel hp hp4 n (generators j)) h h')
        (lpsSparseXDecode x) (lpsSparseQubitDecode qubit) := by sorry
