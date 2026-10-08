-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_has_multilinear_degree_model
-- name    : PhilipponMultiplicity.closure_action_has_multilinear_degree_model
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-05T10:36:46.65179+00:00
-- url     : https://prove2.me/theorems/a8435c6b-f4af-4546-8eb6-07e1f2a7f845
-- title:
--   A finite divisor-class module realizes degree by multilinear intersection forms
-- statement:
--   Let $G$ be a commutative algebraic group over a Philippon base field, let $X$ be its multiprojective closure, and let $\tau_g:X\to X$ be regular automorphisms satisfying $\tau_0=1$ and $\tau_{g+h}=\tau_g\circ\tau_h$.
--
--   There exist a finitely generated abelian group $A$, a representation $\alpha:G(K)\to\operatorname{Aut}(A)$, and classes $c_i\in A$ indexed by the projective factors with the following property. For every closed subset $V\subseteq X$, put $d=\dim V$, with the dimension convention of the mission's Hilbert polynomial. There is a $\mathbb Z$-multilinear form
--   $$
--   I_V:A^d\longrightarrow\mathbb Q
--   $$
--   such that, for all $g\in G(K)$ and all block degrees $D_i\geq1$,
--   $$
--   H(\tau_g(V);D)=I_V\bigl(\alpha(-g)c_D,\ldots,\alpha(-g)c_D\bigr),
--   \qquad c_D=\sum_iD_i c_i.
--   $$
--   Here $H$ is the actual factorial-normalized degree form of the multigraded Hilbert polynomial. The same $A$, $\alpha$, and classes $c_i$ serve all closed subsets and degree vectors; $I_V$ depends only on $V$. Torsion in $A$ is allowed. Empty and reducible closed subsets are included, and a form with no arguments is interpreted as a constant.
--
--   This supplies numerical intersection data for the projective closure in a form that separates geometry from torsion cancellation and finite-presentation arguments.
--
--   **Formalization Note.** This is an auxiliary synthesis of the Theorem of the Base and numerical intersection theory, not a verbatim source theorem. The formal statement requests the indicated finite module, action, and degree formula; it does not define or assert an identification with a pre-existing Neron-Severi object. Construction from the embedded point model, descent of intersection forms, and comparison with the concrete Hilbert degree remain Open. A small carrier type represents the finitely generated group. Neither connectedness nor a jointly regular action is assumed.
--
--   **Current reduction.** The polynomial-to-multilinear construction is proved for finite free modules over any commutative semiring, including degree zero. Restriction of rational scalars and precomposition with the integer-lattice inclusion give the forms required here. The remaining Open input is [the homogeneous degree-polynomial model](https://prove2.me/theorems/a86b669c-a775-4323-841c-55480dd656d5), which constructs the common lattice, action, factor vectors, and homogeneous polynomials representing the actual translated Hilbert degrees. The geometry and Hilbert-degree comparison remain assumptions of this reduction.
-- source:
--   R. Cheng, L. Ji, M. Larson, N. Olander, Theorem of the Base, author version July 1, 2021, Lemma 2.8 (p.7), Proposition 4.3 (p.13), and Theorem 7.4 (p.18), https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf . Stacks Project, Section 33.45 (tag 0BEL), Definition 33.45.3, Lemmas 33.45.5–7, and Definition 33.45.10, https://stacks.math.columbia.edu/tag/0BEL ; Lemma 42.41.4 (tag 0BFI), https://stacks.math.columbia.edu/tag/0BFI . Auxiliary synthesis: finite generation of NS(X), intersection multilinearity and descent modulo algebraic equivalence, and pullback under each individual regular automorphism. Inverse pullback gives a representation; evaluating at -g gives the pullback along tau_g. The coordinate-scheme construction and the comparison with the mission Hilbert polynomial are explicit remaining obligations.

import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem closure_action_has_multilinear_degree_model
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A)
      (_ : Module.Finite ℤ A) (α : Multiplicative G.Point →* (A ≃ₗ[ℤ] A))
      (c : G.FactorIndex → A),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ I : MultilinearMap ℤ
          (fun _ : Fin (SectionThree.locusDimension G.ambient (Subtype.val '' V)) => A) ℚ,
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              I (fun _ => α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i)) := by sorry

end PhilipponMultiplicity
