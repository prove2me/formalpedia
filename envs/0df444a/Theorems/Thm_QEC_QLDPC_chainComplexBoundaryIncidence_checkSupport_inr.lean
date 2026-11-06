-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
-- name    : QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:20:18.697178+00:00
-- url     : https://prove2.me/theorems/561b3149-bee2-4684-9e18-d778d06cc843
-- title:
--   QLDPC: chain Complex Boundary Incidence check Support inr
-- statement:
--   The QLDPC construction uses the chain Complex Boundary Incidence check Support inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L537-L547
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L537-L547

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
    {F : Type u} {ι κ lambda : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData F (Coding.Word F κ) (Coding.Word F ι)
      (Coding.Word F lambda)) (l : lambda) :
    (chainComplexBoundaryIncidence K).checkSupport (Sum.inr l) =
      Coding.hammingSupport
        (K.boundary2 (Coding.canonicalBasisWord (F := F) l)) := by sorry
