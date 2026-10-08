-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_has_dimension_preserving_polynomial_model
-- name    : PhilipponMultiplicity.closure_action_has_dimension_preserving_polynomial_model
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-07T07:17:50.069985+00:00
-- url     : https://prove2.me/theorems/d3241353-4464-479b-9c70-1fae9ceac1b1
-- title:
--   A polynomial degree model with preserved Hilbert dimensions
-- statement:
--   Let $G$ be a commutative algebraic group over a Philippon base field, let $X$ be its multiprojective closure, and suppose regular automorphisms $\tau_g:X\to X$ satisfy $\tau_0=1$ and $\tau_{g+h}=\tau_g\circ\tau_h$.
--
--   There exist a nonnegative integer $m$, a representation $\alpha:G(K)\to\operatorname{Aut}_{\mathbb Z}(\mathbb Z^m)$, and vectors $c_i\in\mathbb Z^m$ indexed by the projective factors, with the following property. For each closed subset $V\subseteq X$, there is a polynomial $P_V\in\mathbb Q[T_1,\ldots,T_m]$ such that
--   $$
--   d(\tau_gV)=d(V),\qquad
--   H(\tau_gV;D)=P_V\!\left(\alpha(-g)\sum_iD_i c_i\right)
--   \quad(g\in G(K),\ D_i\ge1).
--   $$
--   Here $d$ is the total degree of the actual multigraded quotient Hilbert polynomial of the ambient vanishing ideal. The function $H$ evaluates its top homogeneous component multiplied by the factorial of its total degree. The lattice argument is included coordinatewise in $\mathbb Q^m$. The same lattice, representation, and factor vectors work for every closed subset; only the polynomial depends on $V$.
--
--   No homogeneity or degree bound is required of $P_V$ in this conclusion. Empty and reducible closed subsets are included. Neither connectedness nor joint regularity of the action is assumed.
--
--   **Formalization Note.** This is an auxiliary synthesis of the Theorem of the Base and numerical intersection theory, not a verbatim numbered source theorem. The lattice is requested without asserting an identification with an existing Neron-Severi object. Construction from the embedded point model, descent to divisor classes modulo torsion, and comparison with the concrete Hilbert polynomial remain Open.
--
--   **Current reduction.** Hilbert-dimension preservation is proved from [a polynomial model whose total degree is bounded by the original Hilbert dimension](https://prove2.me/theorems/131597ff-45f3-4f37-b760-ce04bfa06322). For nonempty loci, positivity and exact scaling force the translated dimension to be at most that polynomial degree. The regular inverse translation supplies the opposite inequality; empty loci are immediate. The proof retains the child's polynomial and degree identity. Construction of the common lattice and bounded polynomial model is the single remaining Open input.
-- source:
--   R. Cheng, L. Ji, M. Larson, N. Olander, Theorem of the Base, author version July 1, 2021, Lemma 2.8 (p.7), Lemma 7.2 and Theorem 7.4 (p.18), https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf . Stacks Project, Section 33.45 (Tag 0BEL), Definition 33.45.3, Lemmas 33.45.5–7, and Definition 33.45.10, https://stacks.math.columbia.edu/tag/0BEL . Auxiliary synthesis: the torsion-free Neron-Severi group admits a finite integral basis and the numerical degree is polynomial in its coordinates. Inverse pullback gives the representation convention. Isomorphisms preserve geometric dimension; the assertion here additionally requires identification with the mission Hilbert dimension. The coordinate-scheme construction and both dimension and degree comparisons remain explicit Open obligations. Homogeneous-component extraction from positive integral dilations is proved in the parent reduction.

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem closure_action_has_dimension_preserving_polynomial_model
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
          (∀ g : G.Point,
            SectionThree.locusDimension G.ambient (Subtype.val '' (τ g '' V)) =
              SectionThree.locusDimension G.ambient (Subtype.val '' V)) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              MvPolynomial.eval
                (fun j => (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i) j : ℚ)) P := by sorry

end PhilipponMultiplicity
