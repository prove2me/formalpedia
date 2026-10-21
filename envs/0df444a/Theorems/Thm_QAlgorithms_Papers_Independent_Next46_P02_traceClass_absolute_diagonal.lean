-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_traceClass_absolute_diagonal
-- name    : QAlgorithms.Papers.Independent.Next46.P02.traceClass_absolute_diagonal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:30:46.957069+00:00
-- url     : https://prove2.me/theorems/8cbb2c36-cac1-4f27-b40f-0b90cec0c23b
-- title:
--   Absolute diagonal summability in every orthonormal basis
-- statement:
--   Let $H$ be a complete real or complex Hilbert space and let $T\in\mathcal B_1(H)$. For every complete orthonormal basis $(e_i)_{i\in I}$, the scalar diagonal is absolutely summable:
--
--   $$
--   \sum_{i\in I}|\langle Te_i;e_i\rangle|<\infty.
--   $$
--
--   This is the diagonal assertion of Remark 5.4(b), reading its printed $e_k$ as $e_\gamma$ consistently with Claim 3(i). The parenthetical strict trace-norm bound is not used; the valid non-strict bound appears in the trace-properties item.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 14, §5, Remark 5.4(b): absolute diagonal summability

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF p.14, Remark 5.4(b): absolute summability of the basisDiagonal in EVERY basis.
Printed e_k is read as e_gamma using Claim 3(i); the erroneous parenthetical strict
inequality is not asserted. Its valid non-strict version is in trace_properties. -/
theorem traceClass_absolute_diagonal {I : Type*} (b : HilbertBasis I F H)
    (T : H →L[F] H) (hT : IsModulusTraceClass T) :
    Summable (fun i => ‖basisDiagonal b T i‖) := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
