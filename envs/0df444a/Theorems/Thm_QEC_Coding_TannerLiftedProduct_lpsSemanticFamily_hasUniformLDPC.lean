-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSemanticFamily_hasUniformLDPC
-- name    : QEC.Coding.TannerLiftedProduct.lpsSemanticFamily_hasUniformLDPC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:22:56.567099+00:00
-- url     : https://prove2.me/theorems/256def46-ef4f-4ac5-a010-a92001d9385f
-- title:
--   Tanner Lifted Product: lps Semantic Family has Uniform LDPC
-- statement:
--   Every LPS semantic family has one locality bound independent of the
--   residue-prime index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCodeFamily.lean#L45-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCodeFamily.lean#L45-L54

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCodeFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ} {F R R' : Type}
variable [Field F] [Fintype F]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4ca0e95502_22
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4ca0e95502_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4ca0e95502_26

theorem QEC.Coding.TannerLiftedProduct.lpsSemanticFamily_hasUniformLDPC
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1)
    (h : Matrix R (Fin (p + 1)) F)
    (h' : Matrix R' (Fin (p + 1)) F) :
    QEC.QLDPC.HasUniformLDPC
      (lpsSemanticFamily hp hp4 hCount h h') := by sorry
