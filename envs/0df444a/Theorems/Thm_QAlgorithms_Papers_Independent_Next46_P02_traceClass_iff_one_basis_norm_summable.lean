-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_traceClass_iff_one_basis_norm_summable
-- name    : QAlgorithms.Papers.Independent.Next46.P02.traceClass_iff_one_basis_norm_summable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:30:05.029158+00:00
-- url     : https://prove2.me/theorems/a2bb9fbd-aefc-45a0-a8d8-457337d0d143
-- title:
--   One-basis norm summability characterizes trace class
-- statement:
--   Let $T$ be a bounded endomorphism of a complete real or complex Hilbert space $H$. Then
--
--   $$
--   T\in\mathcal B_1(H)\iff
--   \text{there exists a complete orthonormal basis }(e_i)_{i\in I}\text{ with }
--   \sum_{i\in I}\|Te_i\|<\infty.
--   $$
--
--   The basis is existentially quantified. This gives a criterion different from absolute diagonal summability in an arbitrary fixed basis.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 14, §5, Remark 5.4(a): one-basis norm-summability criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF p.14, Remark 5.4(a): existence of ONE norm-summable complete basis. -/
theorem traceClass_iff_one_basis_norm_summable (T : H →L[F] H) :
    IsModulusTraceClass T ↔ ∃ (s : Set H) (b : HilbertBasis s F H),
      Summable (fun i => ‖T (b i)‖) := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
