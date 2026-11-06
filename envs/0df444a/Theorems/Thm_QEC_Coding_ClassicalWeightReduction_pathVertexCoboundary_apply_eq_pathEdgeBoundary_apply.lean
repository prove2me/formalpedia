-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_pathVertexCoboundary_apply_eq_pathEdgeBoundary_apply
-- name    : QEC.Coding.ClassicalWeightReduction.pathVertexCoboundary_apply_eq_pathEdgeBoundary_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:47.987471+00:00
-- url     : https://prove2.me/theorems/49b6bb93-a45b-437e-abc7-bd151ca83fcb
-- title:
--   Classical Weight Reduction: path Vertex Coboundary apply eq path Edge Boundary apply
-- statement:
--   Incidence of a vertex with a truncated path edge is symmetric between
--   the predecessor/successor and endpoint descriptions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L172-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L172-L194

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [Fintype F] [DecidableEq F] [Fintype Check]

theorem QEC.Coding.ClassicalWeightReduction.pathVertexCoboundary_apply_eq_pathEdgeBoundary_apply {n : Nat}
    (i : Fin n) (j : Fin (n - 1)) :
    (optionalSingle (F := F) (pathPrevious i) +
        optionalSingle (F := F) (pathNext i)) j =
      (Pi.single (pathLeft j) 1 + Pi.single (pathRight j) 1 : Word F (Fin n)) i := by sorry
