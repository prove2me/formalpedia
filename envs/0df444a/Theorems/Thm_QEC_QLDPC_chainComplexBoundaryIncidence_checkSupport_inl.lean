-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
-- name    : QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:20:11.621817+00:00
-- url     : https://prove2.me/theorems/6fd0f0d4-c4d4-4bba-8d6f-a0ba681ad1ed
-- title:
--   QLDPC: chain Complex Boundary Incidence check Support inl
-- statement:
--   The QLDPC construction uses the chain Complex Boundary Incidence check Support inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L523-L534
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L523-L534

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
    {F : Type u} {ι κ lambda : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData F (Coding.Word F κ) (Coding.Word F ι)
      (Coding.Word F lambda)) (k : κ) :
    (chainComplexBoundaryIncidence K).checkSupport (Sum.inl k) =
      Coding.hammingSupport
        (Coding.wordLinearMapTranspose K.boundary1
          (Coding.canonicalBasisWord (F := F) k)) := by sorry
