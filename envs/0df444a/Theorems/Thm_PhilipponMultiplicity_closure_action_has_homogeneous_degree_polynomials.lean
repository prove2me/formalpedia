-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_has_homogeneous_degree_polynomials
-- name    : PhilipponMultiplicity.closure_action_has_homogeneous_degree_polynomials
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-07T05:52:26.38502+00:00
-- url     : https://prove2.me/theorems/a86b669c-a775-4323-841c-55480dd656d5
-- title:
--   Translated degrees are homogeneous polynomials on a finite integer lattice
-- statement:
--   Let $G$ be a commutative algebraic group over a Philippon base field, and let $X$ be its multiprojective closure. Suppose that regular automorphisms $\tau_g:X\to X$ satisfy $\tau_0=1$ and $\tau_{g+h}=\tau_g\circ\tau_h$.
--
--   There exist a nonnegative integer $m$, a representation $\alpha:G(K)\to\operatorname{Aut}_{\mathbb Z}(\mathbb Z^m)$, and vectors $c_i\in\mathbb Z^m$ indexed by the projective factors, with the following property. For each closed subset $V\subseteq X$, put $d=\dim V$, using the mission's Hilbert-polynomial dimension. There is a homogeneous polynomial $P_V\in\mathbb Q[T_1,\ldots,T_m]$ of degree $d$ such that
--   $$
--   H(\tau_g(V);D)=P_V\!\left(\alpha(-g)\sum_iD_i c_i\right)
--   \qquad(g\in G(K),\ D_i\ge1).
--   $$
--   The integer vector on the right is evaluated through its coordinatewise inclusion in $\mathbb Q^m$. Here $H$ is the factorial-normalized top homogeneous part of the actual multigraded quotient Hilbert polynomial. The lattice, action, and vectors are shared by all $V$; only $P_V$ depends on $V$.
--
--   This formulation isolates the geometric degree calculation as a polynomial on a finite integer lattice. It includes reducible and empty closed subsets. Degree-zero polynomials are constant, and the zero polynomial is homogeneous in every degree.
--
--   **Formalization Note.** This is an auxiliary synthesis of numerical intersection theory and the Theorem of the Base, not a verbatim numbered source theorem. The statement requests the lattice and degree identity without identifying the lattice with a previously defined Neron-Severi group. Construction from the embedded point model, descent of degree to divisor classes modulo torsion, and comparison with the concrete Hilbert polynomial remain Open. Neither connectedness nor joint regularity of the action is assumed.
--
--   **Current reduction.** Homogeneous-component extraction is proved from positive integer scaling along each lattice direction. The actual Hilbert degree form satisfies the required scaling law directly by definition. The remaining Open input is [an ordinary polynomial degree model with preserved Hilbert dimensions](https://prove2.me/theorems/d3241353-4464-479b-9c70-1fae9ceac1b1); no homogeneity or degree bound is requested of its polynomial. The reduction takes its component in the original Hilbert dimension. The geometric model and the comparison of geometric and Hilbert dimensions remain assumptions.
-- source:
--   R. Cheng, L. Ji, M. Larson, N. Olander, Theorem of the Base, author version July 1, 2021, Lemma 2.8 (p.7), Lemma 7.2 and Theorem 7.4 (p.18), https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf . Stacks Project, Section 33.45 (Tag 0BEL), Definition 33.45.3, Lemmas 33.45.5–7, and Definition 33.45.10, https://stacks.math.columbia.edu/tag/0BEL ; Lemma 42.41.4 (Tag 0BFI), https://stacks.math.columbia.edu/tag/0BFI . Auxiliary synthesis: take the torsion-free quotient of the finitely generated Neron-Severi group, choose an integral basis, and express the degree intersection form as a homogeneous polynomial in that basis. Inverse pullback induces alpha; alpha(-g) represents pullback along tau_g. Constructing the scheme from the embedded point model and identifying its intersection degree with the mission Hilbert degree are explicit remaining obligations. The parent reduction proves the polynomial-to-multilinear algebra independently of these geometric obligations.

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem closure_action_has_homogeneous_degree_polynomials
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (m : ℕ)
      (α : Multiplicative G.Point →* ((Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ)))
      (c : G.FactorIndex → (Fin m → ℤ)),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ P : MvPolynomial (Fin m) ℚ,
          P.IsHomogeneous (SectionThree.locusDimension G.ambient (Subtype.val '' V)) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              MvPolynomial.eval
                (fun j => (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i) j : ℚ)) P := by sorry

end PhilipponMultiplicity
