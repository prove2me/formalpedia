-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P08_boundedVectorDensity
-- name    : QAlgorithms.Papers.Independent.Gap48.P08.boundedVectorDensity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:10:36.273714+00:00
-- url     : https://prove2.me/theorems/78f01303-2bd7-475f-adb7-d603b60c1350
-- title:
--   Density of the intrinsic bounded-vector domain
-- statement:
--   Let $S$ and $H$ be separable complex Hilbert spaces, let $A\subseteq B(S)$ be a unital von Neumann algebra, and let $\rho:A\to B(H)$ be a normal unital complex-linear $*$-representation. Let $\Omega\in S$ be cyclic and separating for $A$, with no norm-one requirement. Define
--   $$
--   D_{\rho,\Omega}=\{\xi\in H:\text{ there is a bounded complex-linear }T:S\to H\text{ with }T(a\Omega)=\rho(a)\xi\text{ for every }a\in A\}.
--   $$
--   Then
--   $$
--   \overline{D_{\rho,\Omega}}=H.
--   $$
--   This gives the dense domain for the analytic relative tensor map. In the paper's notation, $A=R(M)$ is the standard right-action algebra, a copy of the opposite algebra of $M$, $S=L^2(M)$, and $\Omega=\phi^{1/2}$ represents the faithful normal finite functional $\phi$. The set above is the intrinsic definition of $D(H,\phi)$ on PDF p.10. Conversely a cyclic separating realization as above gives such a faithful finite-functional standard representation, so this formulation retains the full scope of the density assertion.
--
--   **Formalization Note** Normality is expressed as preservation of nonempty directed positive suprema. Unitality supplies nondegeneracy; neither faithfulness of $\rho$ nor normalization of $\Omega$ is imposed. Separability of the faithful standard representation ensures separable predual. The independent coordinate strong-sum characterization is a separate deferred node.
-- source:
--   Relative tensor products for modules over von Neumann algebras, arXiv:math/0301061v1, PDF p. 9, §5, bounded-vector density

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P08

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Gap48.P08

variable {S K : Type*}

variable [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Bounded-vector density, §5, PDF p.9, using its intrinsic definition on
PDF p.10. A is R(M), not the left-action copy of M. The bicommutant hypothesis
makes A a concrete von Neumann algebra. The cyclic separating vector omega
represents the faithful normal finite functional phi without normalizing it.
The separable standard space gives a separable predual; rho is normal and
unital, hence nondegenerate, and need not be faithful. K is the source's
right M-module. Neither a row/column classification nor an RTP equivalence
is assumed. The coordinate/intrinsic comparison is separately deferred. -/
theorem boundedVectorDensity [SecondCountableTopology S] [SecondCountableTopology K]
    (A : StarSubalgebra ℂ (S →L[ℂ] S))
    (hA : Set.centralizer (Set.centralizer (A : Set (S →L[ℂ] S))) =
      (A : Set (S →L[ℂ] S)))
    (rho : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (hnormal : IsNormalRepresentation A rho)
    (omega : S)
    (hcyclic : Dense (Set.range (fun a : A => A.subtype a omega)))
    (hseparating : ∀ a : A, A.subtype a omega = 0 → a = 0) :
    Dense (boundedVectorDomain A rho omega) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P08
