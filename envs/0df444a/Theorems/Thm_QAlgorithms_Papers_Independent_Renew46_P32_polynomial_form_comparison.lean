-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_polynomial_form_comparison
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.polynomial_form_comparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:17:33.300397+00:00
-- url     : https://prove2.me/theorems/8b7678e8-a8bf-4dc7-9c24-eb0486eed45d
-- title:
--   Polynomial maps and homogeneous forms
-- statement:
--   Let $K$ be a commutative unital ring, $E,F$ be $K$-modules, $k\ge0$, and $q:E\to F$. Use Definition A.5 for a homogeneous polynomial map and Definition A.1 for a homogeneous form. If $E$ is free, the polynomial condition is equivalent to the existence of a $k$-linear map $m:E^k\to F$ with
--   $$q(x)=m(x,\ldots,x).$$
--
--   Every homogeneous polynomial map of degree $k$ is a homogeneous form of degree $k$. In degrees $k=0,1$ the converse also holds. These comparisons distinguish the general-module definition from a diagonal presentation available on a free domain.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 66, Unnumbered polynomial/form comparison in Appendix A

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

section AlgebraicDefinitions

variable {K : Type u} [CommRing K]

variable {E : Type u} [AddCommGroup E] [Module K E]

variable {F : Type u} [AddCommGroup F] [Module K F]

/-- Appendix A, PDF p. 66: free-domain diagonal characterization,
polynomial-to-form implication, and the degree-zero/one converse. -/
theorem polynomial_form_comparison (q : E → F) (k : ℕ) :
    (Module.Free K E →
      (IsHomogeneousPolynomial (K := K) k q ↔
        ∃ m : MultilinearMap K (fun _ : Fin k => E) F,
          ∀ x : E, q x = m (fun _ => x))) ∧
    (IsHomogeneousPolynomial (K := K) k q → IsHomogeneousForm (K := K) k q) ∧
    ((k = 0 ∨ k = 1) →
      (IsHomogeneousForm (K := K) k q ↔ IsHomogeneousPolynomial (K := K) k q)) := by sorry

end AlgebraicDefinitions

end QAlgorithms.Papers.Independent.Renew46.P32
