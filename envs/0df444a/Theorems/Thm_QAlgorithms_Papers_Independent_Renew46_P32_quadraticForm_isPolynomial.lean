-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_quadraticForm_isPolynomial
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.quadraticForm_isPolynomial
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:17:14.125405+00:00
-- url     : https://prove2.me/theorems/454dd5ea-c621-4cff-91f1-ad7d41f2594c
-- title:
--   Quadratic forms are homogeneous polynomial maps
-- statement:
--   Let $K$ be a commutative unital ring, let $E,F$ be $K$-modules, and let $q:E\to F$ be homogeneous of degree two with bilinear polarization $L_2q(0;\cdot,\cdot)$. For every free $K$-module $\widetilde E$ and every surjective linear map $\phi:\widetilde E\to E$, there is a bilinear map $m:\widetilde E^2\to F$ such that
--   $$q(\phi(x))=m(x,x)\qquad(x\in\widetilde E).$$
--
--   Thus $q$ is a homogeneous polynomial map of degree two in Definition A.5. The domain need not be free, and characteristic two is included.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 66, Lemma A.6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

section AlgebraicDefinitions

variable {K : Type u} [CommRing K]

variable {E : Type u} [AddCommGroup E] [Module K E]

variable {F : Type u} [AddCommGroup F] [Module K F]

/-- Lemma A.6, PDF p. 66: quadratic forms on general modules, including
in characteristic two, meet Definition A.5. -/
theorem quadraticForm_isPolynomial
    (q : E → F) (hq : IsHomogeneousForm (K := K) 2 q) :
    IsHomogeneousPolynomial (K := K) 2 q := by sorry

end AlgebraicDefinitions

end QAlgorithms.Papers.Independent.Renew46.P32
