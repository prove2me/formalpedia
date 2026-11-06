-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_mem_binaryCSSCheckSet
-- name    : QEC.QLDPC.chainComplexCSSRowCheck_mem_binaryCSSCheckSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:24:04.536388+00:00
-- url     : https://prove2.me/theorems/54dbb0d6-95c0-4c01-9a0c-43b0017bbe1f
-- title:
--   QLDPC: chain Complex CSSRow Check mem binary CSSCheck Set
-- statement:
--   The QLDPC construction uses the chain Complex CSSRow Check mem binary CSSCheck Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L283-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L283-L301

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.chainComplexCSSRowCheck_mem_binaryCSSCheckSet
    {ι κ lambda : Type v} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) (c : Sum κ lambda) :
    chainComplexCSSRowCheck K c ∈
      Coding.PauliSymplectic.binaryCSSCheckSet
        K.firstCoboundaryCheckCode K.middleBoundaryCode := by sorry
