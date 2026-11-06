-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
-- name    : QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:20:01.514207+00:00
-- url     : https://prove2.me/theorems/65ffac61-21e1-45da-b94d-b1efb291929d
-- title:
--   QLDPC: chain Complex CSSRow Check weight inl
-- statement:
--   The QLDPC construction uses the chain Complex CSSRow Check weight inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L479-L488
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L479-L488

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
    {ι κ lambda : Type v} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) (k : κ) :
    Coding.PauliSymplectic.weight (chainComplexCSSRowCheck K (Sum.inl k)) =
      Coding.HammingWeight
        (Coding.wordLinearMapTranspose K.boundary1
          (Coding.canonicalBasisWord (F := ZMod 2) k)) := by sorry
