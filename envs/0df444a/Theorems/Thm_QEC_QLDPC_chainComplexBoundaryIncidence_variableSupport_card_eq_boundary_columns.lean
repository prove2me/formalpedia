-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
-- name    : QEC.QLDPC.chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:38:57.309704+00:00
-- url     : https://prove2.me/theorems/85439544-e475-4f33-be40-f387db15f8a7
-- title:
--   QLDPC: chain Complex Boundary Incidence variable Support card eq boundary columns
-- statement:
--   A qubit's incidence degree is exactly the sum of the two boundary-column
--   weights.  The two summands are disjoint because the check index is a sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L566-L621
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L566-L621

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
    {F : Type u} {I K L : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [Fintype K] [Fintype L]
    (C : Coding.ChainComplexData F (Coding.Word F K) (Coding.Word F I)
      (Coding.Word F L)) (q : I) :
    ((chainComplexBoundaryIncidence C).variableSupport q).card =
      Coding.HammingWeight
        (C.boundary1 (Coding.canonicalBasisWord (F := F) q)) +
      Coding.HammingWeight
        (Coding.wordLinearMapTranspose C.boundary2
          (Coding.canonicalBasisWord (F := F) q)) := by sorry
