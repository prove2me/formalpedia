-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
-- name    : QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:20:09.289719+00:00
-- url     : https://prove2.me/theorems/d6a39faa-bb26-4cdb-86e0-8bce7a860d58
-- title:
--   QLDPC: chain Complex Boundary Incidence incident inr
-- statement:
--   The QLDPC construction uses the chain Complex Boundary Incidence incident inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L513-L520
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L513-L520

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
    {F : Type u} {ι κ lambda : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData F (Coding.Word F κ) (Coding.Word F ι)
      (Coding.Word F lambda)) (l : lambda) (q : ι) :
    (chainComplexBoundaryIncidence K).incident (Sum.inr l) q ↔
      (K.boundary2 (Coding.canonicalBasisWord (F := F) l)) q ≠ 0 := by sorry
