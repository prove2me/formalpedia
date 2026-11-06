-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
-- name    : QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:20:22.158019+00:00
-- url     : https://prove2.me/theorems/6055671a-7e89-4bfd-beec-d61b5d7c3e1b
-- title:
--   QLDPC: chain Complex Boundary Incidence incident inl
-- statement:
--   The QLDPC construction uses the chain Complex Boundary Incidence incident inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L502-L510
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L502-L510

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
    {F : Type u} {ι κ lambda : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData F (Coding.Word F κ) (Coding.Word F ι)
      (Coding.Word F lambda)) (k : κ) (q : ι) :
    (chainComplexBoundaryIncidence K).incident (Sum.inl k) q ↔
      (Coding.wordLinearMapTranspose K.boundary1
        (Coding.canonicalBasisWord (F := F) k)) q ≠ 0 := by sorry
