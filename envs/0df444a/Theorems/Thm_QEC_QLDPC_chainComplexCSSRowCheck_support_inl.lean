-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
-- name    : QEC.QLDPC.chainComplexCSSRowCheck_support_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:59.628453+00:00
-- url     : https://prove2.me/theorems/5f32a175-fc30-4559-9d2a-993f4fb3b089
-- title:
--   QLDPC: chain Complex CSSRow Check support inl
-- statement:
--   The QLDPC construction uses the chain Complex CSSRow Check support inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L456-L465
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L456-L465

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.chainComplexCSSRowCheck_support_inl
    {ι κ lambda : Type v} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) (k : κ) :
    Coding.PauliSymplectic.support (chainComplexCSSRowCheck K (Sum.inl k)) =
      Coding.hammingSupport
        (Coding.wordLinearMapTranspose K.boundary1
          (Coding.canonicalBasisWord (F := ZMod 2) k)) := by sorry
