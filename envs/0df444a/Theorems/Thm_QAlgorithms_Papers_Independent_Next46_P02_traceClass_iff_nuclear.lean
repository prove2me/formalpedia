-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_traceClass_iff_nuclear
-- name    : QAlgorithms.Papers.Independent.Next46.P02.traceClass_iff_nuclear
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:22:27.987228+00:00
-- url     : https://prove2.me/theorems/d39c8fe7-26f6-4be4-a202-11483be26aac
-- title:
--   Trace-class and nuclear operators coincide isometrically
-- statement:
--   Let $H$ be any complete real or complex Hilbert space, and let $T:H\to H$ be bounded and linear. Trace class is defined independently by summability of the positive diagonal of $|T|=(T^*T)^{1/2}$ in an orthonormal basis. Nuclearity means that $Tx=\sum_k f_k(x)y_k$ with continuous linear functionals $f_k$ and $\sum_k\|f_k\|\|y_k\|<\infty$. The trace norm is the sum of the positive diagonal of $|T|$; the nuclear norm is the infimum of the displayed representation costs. Then
--
--   $$
--   T\in\mathcal B_1(H)\iff T\in\mathcal B_N(H),\qquad
--   \|T\|_1=\|T\|_N\quad(T\in\mathcal B_1(H)).
--   $$
--
--   This identifies two independently defined operator classes and their norms without a dimension or separability restriction.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 17, §6, Theorem 6.1: trace-class equals nuclear, with equality of norms

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF pp.17–18, Theorem 6.1: independent classes agree, and their norms agree
on the class. No invariance of ker(T)-perp under T is assumed. -/
theorem traceClass_iff_nuclear (T : H →L[F] H) :
    (IsModulusTraceClass T ↔ IsNuclear T) ∧
      (IsModulusTraceClass T → modulusTraceNorm T = banachNuclearNorm T) := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
