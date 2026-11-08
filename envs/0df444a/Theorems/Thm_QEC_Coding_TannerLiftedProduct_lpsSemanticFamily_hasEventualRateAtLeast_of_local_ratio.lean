-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSemanticFamily_hasEventualRateAtLeast_of_local_ratio
-- name    : QEC.Coding.TannerLiftedProduct.lpsSemanticFamily_hasEventualRateAtLeast_of_local_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:13:59.991871+00:00
-- url     : https://prove2.me/theorems/04316a97-44be-4e50-90e8-883ed7227f51
-- title:
--   Tanner Lifted Product: lps Semantic Family has Eventual Rate At Least of local ratio
-- statement:
--   The local dimension ratio supplies the requested asymptotic rate for the
--   actual cofinal LPS semantic family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCodeFamily.lean#L58-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCodeFamily.lean#L58-L74

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

theorem QEC.Coding.TannerLiftedProduct.lpsSemanticFamily_hasEventualRateAtLeast_of_local_ratio
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1)
    (h : Matrix R (Fin (p + 1)) F)
    (h' : Matrix R' (Fin (p + 1)) F)
    (rate : ℝ)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * (p + 1) ≤
        (1 - rate) *
          (((p + 1 : ℕ) : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    QEC.QLDPC.HasEventualRateAtLeast
      (lpsSemanticFamily hp hp4 hCount h h') rate := by sorry
