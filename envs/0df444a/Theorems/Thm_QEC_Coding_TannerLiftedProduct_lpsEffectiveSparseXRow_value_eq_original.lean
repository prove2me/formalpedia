-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveSparseXRow_value_eq_original
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveSparseXRow_value_eq_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:56:43.242283+00:00
-- url     : https://prove2.me/theorems/f98e54b7-0fd1-45b2-8de7-a08c73c97e48
-- title:
--   Tanner Lifted Product: lps Effective Sparse XRow value eq original
-- statement:
--   Actual computed X rows represent the original PK22 family boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L495-L512
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L495-L512

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveSparseXRow_value_eq_original {p D r r' : ℕ}
    {F : Type} [Field F] [Fintype F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (x : LPSSparseXIndex (lpsResiduePrimeSequence hp hp4 n).q D r)
    (qubit : LPSSparseQubitIndex (lpsResiduePrimeSequence hp hp4 n).q D r r') :
    lpsSparseRowValue (lpsEffectiveSparseXRow hp hp4 n generators h h' x) qubit =
      LiftedProduct.boundary1Matrix
        (data (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j)) h h')
        (lpsSparseXDecode x) (lpsSparseQubitDecode qubit) := by sorry
