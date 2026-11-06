-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
-- name    : QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:20:07.855468+00:00
-- url     : https://prove2.me/theorems/604a5b88-df4d-4f5d-871a-27e1b0ff5a35
-- title:
--   QLDPC: chain Complex CSSRow Check weight inr
-- statement:
--   The QLDPC construction uses the chain Complex CSSRow Check weight inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L491-L499
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L491-L499

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
    {ι κ lambda : Type v} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) (l : lambda) :
    Coding.PauliSymplectic.weight (chainComplexCSSRowCheck K (Sum.inr l)) =
      Coding.HammingWeight
        (K.boundary2 (Coding.canonicalBasisWord (F := ZMod 2) l)) := by sorry
