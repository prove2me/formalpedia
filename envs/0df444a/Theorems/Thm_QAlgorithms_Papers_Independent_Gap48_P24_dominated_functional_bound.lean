-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P24_dominated_functional_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P24.dominated_functional_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:35:55.06322+00:00
-- url     : https://prove2.me/theorems/fa96f4f9-a569-4889-b48c-7cc5cf035c6e
-- title:
--   Dominated positive-functional upper bound
-- statement:
--   Let $A$ be an arbitrary complex C*-algebra, possibly nonunital, and let $\omega_0,\omega_1\in A^*$ be bounded positive complex-linear functionals. They need not be normalized. Write $\|\cdot\|$ for the ordinary dual operator norm and $\beta(\omega_0,\omega_1)$ for the infimum of $\|\psi_0-\psi_1\|$ over common nondegenerate *-representations $\pi:A\to\mathcal B(K)$ and vectors with $\omega_i(a)=\langle\psi_i,\pi(a)\psi_i\rangle$ for every $a\in A$.
--
--   Suppose there exists $n\in\mathbb N$ such that $n\omega_0-\omega_1$ is a positive functional. Then
--   $$\beta(\omega_0,\omega_1)\le\sqrt{\|\omega_0-\omega_1\|}.$$
--   The value $n=0$ is permitted and forces $\omega_1=0$. This is the dominated special case used for the general functional estimate.
-- source:
--   A Continuity Theorem for Stinespring's Dilation, arXiv:0710.2495v1, PDF p. 15, Lemma 12, referring to (47)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Lemma 12, PDF pp.15–16: retain the natural-number dominance hypothesis.
n=0 is allowed and then forces omega1=0; the algebra need not be unital. 
Source correction disclosure (PLAN identifiers C1, C6):
Printed: C1: Definition 1, PDF p.4, sets beta_pi=2 for an empty fiber and then takes beta=inf_pi beta_pi over all representations.
C6: The dilation formula on PDF p.2 calls pi a star homomorphism without explicitly requiring nondegeneracy.
Changed: C1: Keep the local default 2, but define the global dilation/scalar Bures distance as the infimum over actual common dilation pairs.
C6: Use nondegenerate representations in dilation/GNS fibers (unital on a unital domain). The embedding sigma in Theorem 2 and Proposition 9 remains arbitrary.
Why: C1: For A=C direct-sum C, H=C, T1(a,b)=9a, T2=0, pi(a,b)=b has an empty first fiber, forcing printed beta<=2 although Theorem 1 requires beta>=3. The proofs optimize only common fibers.
C6: The source repeatedly uses V*V=T(1) and norm(V)^2=norm(T(1)) on PDF pp.2-3 and 7. Degenerate pi with an invisible component of V invalidates these identities; nondegeneracy implements the proof convention without normalizing V or restricting CP maps.
-/
theorem dominated_functional_bound {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (omega0 omega1 : A →L[ℂ] ℂ)
    (h0 : IsPositiveFunctional omega0) (h1 : IsPositiveFunctional omega1)
    (hdom : ∃ n : ℕ, IsPositiveFunctional ((n : ℂ) • omega0 - omega1)) :
    scalarBures omega0 omega1 ≤ Real.sqrt ‖omega0 - omega1‖ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P24

end
