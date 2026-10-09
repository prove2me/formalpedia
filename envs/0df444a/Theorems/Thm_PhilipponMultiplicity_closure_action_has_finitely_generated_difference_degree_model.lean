-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_has_finitely_generated_difference_degree_model
-- name    : PhilipponMultiplicity.closure_action_has_finitely_generated_difference_degree_model
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-07T11:39:51.371078+00:00
-- url     : https://prove2.me/theorems/548b0d79-a104-4726-86f3-68c7de75b36a
-- title:
--   A finitely generated class-group model for directional degree differences
-- statement:
--   Let $G$ be a commutative algebraic group over a Philippon base field and $X$ its multiprojective closure. Let $\tau_g:X\to X$ be regular automorphisms with $\tau_0=1$ and $\tau_{g+h}=\tau_g\circ\tau_h$.
--
--   There exist a finitely generated abelian group $A$, a representation $\alpha:G(K)\to\operatorname{Aut}_{\mathbb Z}(A)$, and classes $c_i\in A$ indexed by the projective factors, with the following property. For every closed subset $V\subseteq X$, there is a function $f_V:A\to\mathbb Q$. If $d_V$ is the total degree of the actual multigraded quotient Hilbert polynomial of the ambient vanishing ideal of $V$, then
--   $$
--   \Delta_y^{\,d_V+1}f_V=0\qquad(y\in A),\qquad
--   (\Delta_y f)(z)=f(z+y)-f(z).
--   $$
--   This is an identity at every base point of $A$. The function recovers translated degrees:
--   $$
--   H(\tau_g(V);D)=f_V\!\left(\alpha(-g)\sum_iD_ic_i\right)
--   \qquad(g\in G(K),\ D_i\ge1).
--   $$
--   Here $H$ evaluates the factorial-normalized top homogeneous part of the actual quotient Hilbert polynomial. The group, representation, and factor classes are common to all closed subsets; the function and its degree bound depend on $V$.
--
--   Torsion is allowed in $A$. No basis, torsion-free hypothesis, or invariance of $f_V$ under torsion is required. Empty and reducible closed subsets and degree zero are included. The parent reduction proves that these functions automatically descend to $A/A_{\mathrm{tors}}$, that the same difference bounds survive descent, and that the action and classes transport to a finite integer lattice.
--
--   **Formalization Note.** This is an auxiliary synthesis, not a verbatim numbered source theorem. The intended geometric group is a divisor-class group such as the Néron–Severi group. Constructing the scheme associated with the embedded point model, establishing finite generation and the induced action, defining the numerical functions on the class group, proving their difference identities, and comparing them with the concrete Hilbert degree remain Open. Neither connectedness nor joint regularity of the action is assumed.
--
--   **Verified Euler-characteristic reduction (9 October 2026).** An accepted proof-sketch recovers the degree function as $f_V(a)=\Delta_a^{d_V}\chi_V(0)$ from an [Euler-characteristic model with eventual Hilbert-function agreement](https://prove2.me/theorems/77e06c1b-e30f-483e-a083-76033f52b5a6). It proves the directional bound for $f_V$, identifies the normalized leading coefficient and derives Hilbert-dimension preservation using the inverse action. The construction of the geometric model remains Open. The formal statement is unchanged.
-- source:
--   R. Cheng, L. Ji, M. Larson, N. Olander, Theorem of the Base, Lemma 7.2 (p.18) and Theorem 7.4 (pp.18–19), https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf . Stacks Project, Section 33.45 (Tag 0BEL), Lemma 33.45.1 and its dimension-drop proof, Definition 33.45.3, Lemmas 33.45.5–7 and Definition 33.45.10, https://stacks.math.columbia.edu/tag/0BEL . Auxiliary synthesis: seek a finitely generated divisor-class group with numerical degree functions whose high directional differences vanish. No theorem above is claimed to state the embedded point-model assertion verbatim. Scheme construction, class-group descent, and the actual Hilbert-degree comparison remain Open. The parent proves the elementary torsion invariance and finite lattice construction, using the standard structure theorem for finitely generated modules over the integers.

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem closure_action_has_finitely_generated_difference_degree_model
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A)
      (_ : Module.Finite ℤ A)
      (α : Multiplicative G.Point →* (A ≃ₗ[ℤ] A))
      (c : G.FactorIndex → A),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ f : A → ℚ,
          (∀ y : A,
            (fwdDiff y)^[SectionThree.locusDimension G.ambient (Subtype.val '' V) + 1] f = 0) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              f (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i)) := by sorry

end PhilipponMultiplicity
