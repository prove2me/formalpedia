-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_has_bounded_polynomial_degree_model
-- name    : PhilipponMultiplicity.closure_action_has_bounded_polynomial_degree_model
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-07T07:47:13.035881+00:00
-- url     : https://prove2.me/theorems/131597ff-45f3-4f37-b760-ce04bfa06322
-- title:
--   A polynomial degree model bounded by Hilbert dimension
-- statement:
--   Let $G$ be a commutative algebraic group over a Philippon base field, let $X$ be its multiprojective closure, and suppose regular automorphisms $\tau_g:X\to X$ satisfy $\tau_0=1$ and $\tau_{g+h}=\tau_g\circ\tau_h$.
--
--   There exist an integer $m\ge0$, a representation $\alpha:G(K)\to\operatorname{Aut}_{\mathbb Z}(\mathbb Z^m)$, and vectors $c_i\in\mathbb Z^m$ indexed by the projective factors such that every closed subset $V\subseteq X$ admits $P_V\in\mathbb Q[T_1,\ldots,T_m]$ satisfying
--   $$
--   \deg P_V\le d_V,\qquad
--   H(\tau_g(V);D)=P_V\!\left(\alpha(-g)\sum_iD_ic_i\right)
--   \quad(g\in G(K),\ D_i\ge1).
--   $$
--   Here $d_V$ is the total degree of the actual quotient Hilbert polynomial of the ambient vanishing ideal of $V$. The function $H$ evaluates the top homogeneous component of the corresponding quotient Hilbert polynomial, multiplied by the factorial of its total degree. The integral lattice argument is included coordinatewise in $\mathbb Q^m$. The lattice, representation, and factor vectors are common to all closed subsets. Only the polynomial depends on $V$.
--
--   Empty and reducible closed subsets are included. Lean's total degree of the zero polynomial is zero. No homogeneity of $P_V$, dimension preservation, connectedness, or joint regularity of the action is assumed.
--
--   **Formalization Note.** This is an auxiliary synthesis of the Theorem of the Base and numerical intersection theory, not a verbatim numbered theorem. The abstract lattice is not identified with an existing Neron-Severi object. The scheme realization of the embedded point model, construction and finite generation of divisor classes modulo torsion, the action on those classes, and comparison of the intersection polynomial with the concrete factorial-normalized Hilbert degree remain explicit Open obligations. The parent reduction proves that this degree bound already implies preservation of the concrete Hilbert dimension.
--
--   **Current reduction.** A checked integer-lattice interpolation argument reduces this theorem to [a numerical degree function polynomial on every integer affine line](https://prove2.me/theorems/90797c3a-07cc-4c81-a599-e80c282a91ac). Repeated Lagrange interpolation constructs the multivariate polynomial. Integer-ray identities and the nonvanishing of its highest homogeneous component establish the same total-degree bound. The common lattice, representation, factor vectors, linewise degree functions, and their comparison with the actual Hilbert degree remain Open. The formal statement is unchanged.
-- source:
--   R. Cheng, L. Ji, M. Larson, N. Olander, Theorem of the Base, author version July 1, 2021, Lemma 2.8 (p.7), Lemma 7.2 and Theorem 7.4 (p.18), https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf . Stacks Project, Section 33.45 (Tag 0BEL), Lemma 33.45.1, Definition 33.45.3, Lemmas 33.45.5–7 and Definition 33.45.10, https://stacks.math.columbia.edu/tag/0BEL . Auxiliary synthesis: the torsion-free Neron-Severi group has a finite integral basis, and numerical intersection degree is polynomial in divisor coordinates with degree bounded by the dimension. Inverse pullback supplies the representation convention. The point-model scheme realization and equality with the mission Hilbert invariants are not supplied by these citations alone and remain part of this Open assertion. The parent proves Hilbert-dimension preservation from the degree bound by positivity and positive-integer scaling, followed by inverse translation.

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem closure_action_has_bounded_polynomial_degree_model
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
          P.totalDegree ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              MvPolynomial.eval
                (fun j => (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i) j : ℚ)) P := by sorry

end PhilipponMultiplicity
