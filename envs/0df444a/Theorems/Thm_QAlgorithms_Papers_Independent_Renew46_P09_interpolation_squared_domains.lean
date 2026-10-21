-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P09_interpolation_squared_domains
-- name    : QAlgorithms.Papers.Independent.Renew46.P09.interpolation_squared_domains
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:03:55.715817+00:00
-- url     : https://prove2.me/theorems/f1682d86-38c4-4e96-90a5-13235328be73
-- title:
--   Proposition 2.1: interpolation estimate
-- statement:
--   Let $H$ be a real or complex Hilbert space and let $A$ and $B$ be densely defined positive self-adjoint operators with inverses on their ranges; these inverses may be unbounded. Let $T\in B(H)$ and $C\ge0$. Suppose
--
--   $$
--   T(D(A^2))\subseteq D(B^2),\qquad
--   \|B^2Tv\|\le C\|A^2v\|\quad(v\in D(A^2)).
--   $$
--
--   Then
--
--   $$
--   T(D(A))\subseteq D(B),\qquad
--   \|BTv\|\le\sqrt{\|T\|C}\,\|Av\|\quad(v\in D(A)).
--   $$
--
--   This estimate transfers a squared-operator bound to the first powers while retaining their actual domains.
--
--   **Formalization Note** Injectivity encodes existence of the possibly unbounded inverses. A vector in the squared domain carries both membership in $D(A)$ and membership of its first image in $D(A)$. Image witnesses express the range inclusions and the norm estimates together.
-- source:
--   On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, PDF p. 9, Proposition 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P09

noncomputable section

open MeasureTheory Filter

open scoped Manifold ContDiff Topology

namespace QAlgorithms.Papers.Independent.Renew46.P09

/-- Proposition 2.1, PDF p.9: interpolation from squared domains to first
powers, with constant sqrt(norm(T) * C). Injectivity expresses the source's
possibly unbounded inverses; bounded invertibility is not assumed.
The witnesses are domain elements for the images of T, so both range inclusions
and both estimates concern the full indicated domains. -/
theorem interpolation_squared_domains
    {K H : Type*} [RCLike K]
    [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]
    (A B : H →ₗ.[K] H)
    (hA : IsPositiveSelfAdjoint A) (hB : IsPositiveSelfAdjoint B)
    (hAinjective : Function.Injective A) (hBinjective : Function.Injective B)
    (T : H →L[K] H) (C : ℝ) (hC : 0 ≤ C)
    (htwo : ∀ v : SquareDomain A, ∃ w : SquareDomain B,
      (w.val : H) = T (v.val : H) ∧ ‖squareValue B w‖ ≤ C * ‖squareValue A v‖) :
    ∀ v : A.domain, ∃ w : B.domain,
      (w : H) = T (v : H) ∧ ‖B w‖ ≤ Real.sqrt (‖T‖ * C) * ‖A v‖ := by sorry

end QAlgorithms.Papers.Independent.Renew46.P09

end
