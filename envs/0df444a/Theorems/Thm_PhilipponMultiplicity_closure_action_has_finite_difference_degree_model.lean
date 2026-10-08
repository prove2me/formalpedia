-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_has_finite_difference_degree_model
-- name    : PhilipponMultiplicity.closure_action_has_finite_difference_degree_model
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-07T10:48:10.919136+00:00
-- url     : https://prove2.me/theorems/331f9519-5f91-4b61-b2e9-1109397104f8
-- title:
--   A lattice degree function with vanishing directional finite differences
-- statement:
--   Let $G$ be a commutative algebraic group over a Philippon base field, let $X$ be its multiprojective closure, and suppose regular automorphisms $\tau_g:X\to X$ satisfy $\tau_0=1$ and $\tau_{g+h}=\tau_g\circ\tau_h$.
--
--   There exist an integer $m\ge0$, a representation $\alpha:G(K)\to\operatorname{Aut}_{\mathbb Z}(\mathbb Z^m)$, and vectors $c_i\in\mathbb Z^m$ indexed by the projective factors with the following property. Every closed subset $V\subseteq X$ admits a function $f_V:\mathbb Z^m\to\mathbb Q$. Put $d_V$ equal to the total degree of the actual multigraded quotient Hilbert polynomial of the ambient vanishing ideal of $V$. Define the directional difference by
--   $$
--   (\Delta_y f)(z)=f(z+y)-f(z).
--   $$
--   For every lattice direction, the iterated difference vanishes identically:
--   $$
--   \Delta_y^{\,d_V+1} f_V=0\qquad(y\in\mathbb Z^m).
--   $$
--   The function also satisfies the translated degree identity
--   $$
--   H(\tau_g(V);D)=f_V\!\left(\alpha(-g)\sum_iD_ic_i\right)
--   \qquad(g\in G(K),\ D_i\ge1),
--   $$
--   where $H$ evaluates the factorial-normalized top homogeneous part of the actual quotient Hilbert polynomial. The lattice, representation, and factor vectors are shared by all closed subsets; only the degree function depends on $V$.
--
--   This formulation isolates the geometric finite-difference vanishing expected from dimension drop under divisor intersections. The vanishing holds at every lattice base point and in every direction, including negative coordinates. Empty and reducible closed subsets, dimension zero, and the zero-dimensional lattice are included.
--
--   **Formalization Note.** This is an auxiliary synthesis of the Theorem of the Base and numerical intersection theory. An accepted reduction proves torsion invariance of rational functions with nilpotent directional differences, descent of their degree bounds, and transport of a common action and factor classes to a finite integer lattice. Its sole remaining geometric input is [a finitely generated class-group model](https://prove2.me/theorems/548b0d79-a104-4726-86f3-68c7de75b36a), which permits torsion and assumes no basis or torsion invariance. Constructing the scheme and class group, proving finite generation and the numerical difference identities, and comparing the functions with the actual Hilbert degree remain Open. Neither connectedness nor joint regularity of the action is assumed.
-- source:
--   R. Cheng, L. Ji, M. Larson, N. Olander, Theorem of the Base, Lemma 2.8 (p.7), Lemma 7.2 and Theorem 7.4 (pp.18–19), https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf . Stacks Project, Section 33.45 (Tag 0BEL), Lemma 33.45.1 and its dimension-drop finite-difference proof, Definition 33.45.3, Lemmas 33.45.5–7 and Definition 33.45.10, https://stacks.math.columbia.edu/tag/0BEL . Auxiliary synthesis: finite generation modulo torsion supplies a lattice; the degree function has vanishing differences beyond the dimension in every lattice direction. The point-model scheme construction, numerical descent, and actual Hilbert-degree comparison remain part of this Open theorem. The parent proves the arithmetic implication from finite-difference vanishing to polynomial restrictions on all integer affine lines. Its discrete antiderivative uses the Bernoulli identity DLMF 24.4.1, https://dlmf.nist.gov/24.4.E1 .

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem closure_action_has_finite_difference_degree_model
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
        ∃ f : (Fin m → ℤ) → ℚ,
          (∀ y : Fin m → ℤ,
            (fwdDiff y)^[SectionThree.locusDimension G.ambient (Subtype.val '' V) + 1] f = 0) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              f (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i)) := by sorry

end PhilipponMultiplicity
