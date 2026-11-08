-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveSparseZRow_value_eq_original
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveSparseZRow_value_eq_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:56:53.944526+00:00
-- url     : https://prove2.me/theorems/9b130051-8b32-475a-9305-af093187db05
-- title:
--   Tanner Lifted Product: lps Effective Sparse ZRow value eq original
-- statement:
--   Actual computed Z rows represent the original PK22 family boundary transpose.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L515-L532
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L515-L532

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveSparseZRow_value_eq_original {p D r r' : ℕ}
    {F : Type} [Field F] [Fintype F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (z : LPSSparseZIndex (lpsResiduePrimeSequence hp hp4 n).q D r')
    (qubit : LPSSparseQubitIndex (lpsResiduePrimeSequence hp hp4 n).q D r r') :
    lpsSparseRowValue (lpsEffectiveSparseZRow hp hp4 n generators h h' z) qubit =
      LiftedProduct.boundary2Matrix
        (data (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j)) h h')
        (lpsSparseQubitDecode qubit) (lpsSparseZDecode z) := by sorry
