-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
-- name    : QEC.QLDPC.chainComplexCSSRowCheck_support_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:20:37.122971+00:00
-- url     : https://prove2.me/theorems/e8fbd5d0-d7d8-4b3e-911f-dd8c403db227
-- title:
--   QLDPC: chain Complex CSSRow Check support inr
-- statement:
--   The QLDPC construction uses the chain Complex CSSRow Check support inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L468-L476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L468-L476

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.chainComplexCSSRowCheck_support_inr
    {ι κ lambda : Type v} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) (l : lambda) :
    Coding.PauliSymplectic.support (chainComplexCSSRowCheck K (Sum.inr l)) =
      Coding.hammingSupport
        (K.boundary2 (Coding.canonicalBasisWord (F := ZMod 2) l)) := by sorry
