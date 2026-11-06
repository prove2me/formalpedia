-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
-- name    : QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:20:18.135601+00:00
-- url     : https://prove2.me/theorems/de26267c-2873-4bb4-a87e-91ed65d0c5b3
-- title:
--   QLDPC: chain Complex CSSRow Check support eq check Support
-- statement:
--   The QLDPC construction uses the chain Complex CSSRow Check support eq check Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L624-L633
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L624-L633

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
    {ι κ lambda : Type v} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) (c : Sum κ lambda) :
    Coding.PauliSymplectic.support (chainComplexCSSRowCheck K c) =
      (chainComplexBoundaryIncidence K).checkSupport c := by sorry
