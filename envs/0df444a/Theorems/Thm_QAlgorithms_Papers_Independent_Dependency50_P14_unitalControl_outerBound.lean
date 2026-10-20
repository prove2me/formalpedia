-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P14_unitalControl_outerBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P14.unitalControl_outerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:46:12.088048+00:00
-- url     : https://prove2.me/theorems/71fabad4-a5b0-4863-8ab1-bc31cd43de6a
-- title:
--   Invariant positive cones give an outer bound for unital controlled dynamics
-- statement:
--   Let $N\ge1$ and consider a finite-dimensional unital GKLS system on $\mathrm{her}_0(N)$, the real space of traceless Hermitian matrices. Its Hamiltonian is $H_u=H_d+\sum_{j=1}^{m}u_jH_j$, where the fixed Hamiltonians are Hermitian and traceless and the controls range over all $u\in\mathbb R^m$. Its fixed dissipator is
--
--   $$
--   \Gamma(\rho)=\tfrac12\sum_k(V_k^\dagger V_k\rho+\rho V_k^\dagger V_k-2V_k\rho V_k^\dagger),\qquad \Gamma(I)=0,
--   $$
--
--   with arbitrary finite complex jump matrices $V_k$. Put $A_u=-i[H_u,\cdot]-\Gamma$ and $P_\Sigma=\langle\exp(tA_u):t\ge0,\ u\in\mathbb R^m\rangle_S$. Let $K=\mathrm{Ad}_{\mathrm{SU}(N)}$ act by $\mathrm{Ad}_U(X)=UXU^\dagger$, and let $\mathfrak k=\mathrm{ad}_{\mathfrak{su}(N)}$ be its real Lie algebra on $\mathrm{her}_0(N)$.
--
--   Suppose $c$ is a closed convex pointed cone of self-adjoint positive semidefinite endomorphisms of $\mathrm{her}_0(N)$, relative to the Hilbert–Schmidt inner product $\langle X,Y\rangle=\operatorname{tr}(XY)$. Pointed means $c\cap(-c)=\{0\}$. Assume
--
--   1. $\Gamma|_{\mathrm{her}_0(N)}\in c$.
--   2. $[c,c]\subseteq\mathfrak k$ and $[c,\mathfrak k]\subseteq c-c$, where brackets are operator commutators.
--   3. $\mathrm{Ad}_U c\,\mathrm{Ad}_{U^{-1}}\subseteq c$ for every $U\in\mathrm{SU}(N)$.
--
--   Then
--
--   $$
--   \overline{P_\Sigma}\subseteq S_c:=\exp(-c)K,\qquad
--   \mathcal L(S_c)=(-c)\oplus\mathfrak k.
--   $$
--
--   Both $\overline{P_\Sigma}$ and $S_c$ are Lie subsemigroups. The sum is direct, so $c\cap\mathfrak k=\{0\}$. Closures are relative to $\mathrm{GL}(\mathrm{her}_0(N))$.
--
--   This provides a structural outer approximation to the reachable semigroup, including its outer tangent wedge.
--
--   **Formalization Note** The cone is read as closed from the proof's explicit application of Theorem II.1. The complexifications of endomorphisms on $\mathrm{her}_0(N)$ are extended by zero on $I$; their exponentials fix $I$.
-- source:
--   Lie-Semigroup Structures for Reachability and Control of Open Quantum Systems, arXiv:0811.3906v4, PDF p. 11, Theorem III.5

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P14

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P14

open QAlgorithms.Papers.Independent.Information100.P59 (Operator dissipator)

/-- arXiv:0811.3906v4 PDF pp.11–12, Theorem III.5. The proof's application of
II.1 fixes c as a CLOSED convex pointed cone. All three hypotheses, the closed
reachable bound, outer Lie-subsemigroup property, and direct-sum wedge are retained. -/
theorem unitalControl_outerBound {N m : ℕ} (hN : 0 < N)
    (D : UnitalControl N m) (c : Set (Super N))
    (hc : IsClosedCone c)
    (hpointed : ∀ A ∈ c, -A ∈ c → A = 0)
    (hpositive : ∀ A ∈ c, IsPositiveHomogeneous A)
    (hnoise : relaxationGenerator D.jumps ∈ c)
    (hcc : ∀ A ∈ c, ∀ B ∈ c, A * B - B * A ∈ adjointLieAlgebra N)
    (hck : ∀ A ∈ c, ∀ K ∈ adjointLieAlgebra N,
      ∃ C ∈ c, ∃ E ∈ c, A * K - K * A = C - E)
    (hinvariant : ∀ k ∈ adjointSU N, ∀ A ∈ c,
      (k : Super N) * A * ((k⁻¹ : InvertibleSuper N) : Super N) ∈ c) :
    IsLieSubsemigroup (closure (controlSemigroup D)) ∧
    closure (controlSemigroup D) ⊆ coneSemigroup c ∧
    IsLieSubsemigroup (coneSemigroup c) ∧
    tangent (coneSemigroup c) = coneWedge c ∧
    (∀ A ∈ c, A ∈ adjointLieAlgebra N → A = 0) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P14

end
