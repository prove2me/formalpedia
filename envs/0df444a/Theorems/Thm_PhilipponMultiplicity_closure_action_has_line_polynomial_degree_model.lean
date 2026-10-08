-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_has_line_polynomial_degree_model
-- name    : PhilipponMultiplicity.closure_action_has_line_polynomial_degree_model
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-07T10:22:41.01248+00:00
-- url     : https://prove2.me/theorems/90797c3a-07cc-4c81-a599-e80c282a91ac
-- title:
--   A lattice degree function polynomial on integer affine lines
-- statement:
--   Let $G$ be a commutative algebraic group over a Philippon base field, let $X$ be its multiprojective closure, and suppose regular automorphisms $\tau_g:X\to X$ satisfy $\tau_0=1$ and $\tau_{g+h}=\tau_g\circ\tau_h$.
--
--   There exist an integer $m\ge0$, a representation $\alpha:G(K)\to\operatorname{Aut}_{\mathbb Z}(\mathbb Z^m)$, and vectors $c_i\in\mathbb Z^m$ indexed by the projective factors with the following property. Every closed subset $V\subseteq X$ admits a function $f_V:\mathbb Z^m\to\mathbb Q$. Set $d_V$ equal to the total degree of the actual multigraded quotient Hilbert polynomial of the ambient vanishing ideal of $V$. For every $x,y\in\mathbb Z^m$, there is a univariate polynomial $q_{V,x,y}\in\mathbb Q[T]$ such that
--   $$
--   \deg q_{V,x,y}\le d_V,\qquad
--   f_V(x+ty)=q_{V,x,y}(t)\quad(t\in\mathbb Z).
--   $$
--   The degree function also satisfies
--   $$
--   H(\tau_g(V);D)=f_V\!\left(\alpha(-g)\sum_iD_i c_i\right)
--   \qquad(g\in G(K),\ D_i\ge1),
--   $$
--   where $H$ evaluates the factorial-normalized top homogeneous part of the actual quotient Hilbert polynomial. The lattice, representation, and factor vectors are common to all closed subsets; only the function and its line polynomials depend on $V$.
--
--   This isolates a numerical intersection function on a lattice and the univariate degree calculation on every integral affine line. Empty and reducible closed subsets, zero-dimensional lattices, and negative lattice coordinates are included. The zero polynomial has natural degree zero. No multivariate polynomial is part of the conclusion.
--
--   **Formalization Note.** This is an auxiliary synthesis of the Theorem of the Base and numerical intersection theory, not a verbatim numbered source theorem. Constructing the scheme associated with the embedded point model, descending numerical degree to a finite divisor-class lattice, constructing its action, and identifying its numerical function with the concrete factorial-normalized Hilbert degree remain Open. Neither connectedness nor joint regularity of the action is assumed.
--
--   **Current reduction.** A checked arithmetic argument reduces this theorem to [a degree function with vanishing directional finite differences](https://prove2.me/theorems/331f9519-5f91-4b61-b2e9-1109397104f8). Bernoulli polynomials give discrete antiderivatives, and induction on the order of the difference constructs a univariate polynomial of the required degree on all integers. Restriction to an affine lattice line commutes with iterated differences. The common geometric lattice, action, factor vectors, numerical function, directional vanishing, and actual Hilbert-degree identity remain Open. The formal statement is unchanged.
-- source:
--   R. Cheng, L. Ji, M. Larson, N. Olander, Theorem of the Base, author version July 1, 2021, Lemma 2.8 (p.7), Lemma 7.2 and Theorem 7.4 (pp.18–19), https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf . Stacks Project, Section 33.45 (Tag 0BEL), Lemma 33.45.1, Definition 33.45.3, Lemmas 33.45.5–7 and Definition 33.45.10, https://stacks.math.columbia.edu/tag/0BEL . Auxiliary synthesis: finite generation modulo torsion supplies the integral lattice, and numerical intersection degree restricted to an integral affine line is a univariate polynomial bounded by the dimension. These citations do not by themselves supply the point-model scheme construction or comparison with the mission Hilbert polynomial; those remain obligations of this Open theorem. The parent proves independently, by Lagrange interpolation and integer-ray polynomial identities, that such a linewise function admits a multivariate polynomial of the same total-degree bound.

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem closure_action_has_line_polynomial_degree_model
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
          (∀ x y : Fin m → ℤ, ∃ q : Polynomial ℚ,
            q.natDegree ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
            ∀ t : ℤ, f (fun j => x j + t * y j) = q.eval (t : ℚ)) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              f (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i)) := by sorry

end PhilipponMultiplicity
