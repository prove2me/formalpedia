-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_convex_LOCC_criterion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.convex_LOCC_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:34:31.292553+00:00
-- url     : https://prove2.me/theorems/0e709fdf-954d-4ddf-af39-d6a009b5adf8
-- title:
--   Proposition 3 [18]: convex LOCC criterion (cited/background)
-- statement:
--   Let $f$ be a real-valued convex functional on all finite-dimensional bipartite density matrices. It is an average LOCC monotone if and only if it is invariant under local unitaries and satisfies the local orthogonal-flags identity:
--
--   $$f\left(\sum_i p_i\rho_{AB}^i\otimes |i\rangle\langle i|_X\right)=\sum_i p_i f(\rho_{AB}^i),\qquad X=A'\ \text{or}\ B'.$$
--
--   The $p_i$ are arbitrary finite probability weights, the conditional states may be mixed, and the flag is held by one honest party. LOCC includes adaptive local instruments, local ancillas and disposal. This is the cited criterion of Horodecki [18], checked against Theorem 3 of the original arXiv:quant-ph/0412210, PDF p.2; it is background rather than a new result of this paper.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 4, Proposition 3 [18]: convex LOCC criterion (cited/background)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 3 [18], PDF p.4, independently checked against the original
Horodecki, quant-ph/0412210, Theorem 3, PDF p.2, equations (11),(12).
This is a cited background result, not an original result of this paper.
The plan's absent-source obstacle was removed by this primary-source check. -/
theorem convex_LOCC_criterion (g : FiniteState 2 → ℝ)
    (hconvex : IsConvexFunctional g) :
    IsAdaptiveLOCCMonotone g ↔ IsLocalUnitaryInvariant g ∧ SatisfiesFlags g := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
