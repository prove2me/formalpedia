-- Prove2me | Theorems.Thm_TwoCategory_exists_equivalence_of_quasiInverses
-- name    : TwoCategory.exists_equivalence_of_quasiInverses
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:28.173022+00:00
-- url     : https://prove2.me/theorems/15e10743-cf90-4249-9f65-64daaa4086ff
-- title:
--   A 1-morphism with a left and a right quasi-inverse is an adjoint equivalence (one may take $g=h$)
-- statement:
--   In a bicategory, a 1-morphism that has a left quasi-inverse and a right quasi-inverse is an equivalence whose two quasi-inverses can be taken equal, and it underlies an adjoint equivalence.
--
--   Throughout, $\mathcal C$ is a bicategory (for instance a strict 2-category in the sense of Definition E.5.2.1 of the source). For 1-morphisms $f:A\to B$ and $g:B\to C$ the composite is written $g\circ f$, the identity 1-morphism of $A$ is $1_A$ (the source writes $\bullet_A$), and a *2-isomorphism* is an invertible 2-morphism.
--
--   **Statement.** Let $f:A\to B$ and $g,h:B\to A$ be 1-morphisms of $\mathcal C$ and let
--
--   $$\alpha:1_A\Rightarrow g\circ f,\qquad \beta:f\circ h\Rightarrow 1_B$$
--
--   be 2-isomorphisms (this is the definition of "$f$ is an equivalence" in Definition E.5.2.3(1) of the source). Then $g$ is also a right quasi-inverse of $f$: there is a 2-isomorphism $\varepsilon:f\circ g\Rightarrow 1_B$. More precisely, there are 2-isomorphisms $\eta:1_A\Rightarrow g\circ f$ and $\varepsilon:f\circ g\Rightarrow 1_B$ which satisfy the triangle identity
--
--   $$(\varepsilon\star 1_f)\odot(1_f\star\eta)=1_f$$
--
--   (read modulo the unit and associativity constraints of $\mathcal C$), i.e. $(f,g,\eta,\varepsilon)$ is an adjoint equivalence between $A$ and $B$.
--
--   This is the remark that in the definition of an equivalence in a 2-category one can choose $g=h$; it identifies the two-sided notion of equivalence used in Appendix E of the source (for 2-categories of groupoids, fibered categories and stacks) with the notion of adjoint equivalence of Mathlib's bicategory library.
--
--   **Formalization Note.** Lean composes in diagrammatic order: `f ≫ g` is $g\circ f$. `Bicategory.Equivalence a b` is Mathlib's structure of adjoint equivalences between objects `a`, `b` of a bicategory (fields `hom : a ⟶ b`, `inv : b ⟶ a`, `unit : 𝟙 a ≅ hom ≫ inv`, `counit : inv ≫ hom ≅ 𝟙 b` and the left triangle identity); "$f$ is an equivalence" is rendered as `∃ e : Bicategory.Equivalence a b, e.hom = f`. The conclusion `∃ e : Bicategory.Equivalence a b, e.hom = f ∧ e.inv = g` packages $\eta$, $\varepsilon$ and the triangle identity; the unit of `e` is not asserted to be the given $\alpha$. The triangle identity is slightly more than the source's remark states (which only asserts that one can choose $g=h$); it is the classical refinement of an equivalence to an adjoint equivalence.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 900-901, Remark E.5.2.5(1) (with Definition E.5.2.3(1)); classical reference: the paper cites [GR, Ch. 2, Rem. 2.1.4] at this spot; the entry printed under the key [GR] in the paper's bibliography is an unrelated article (P. Górka, E. G. Reyes, Sobolev spaces on locally compact abelian groups), and the work meant is presumably the bibliography entry [GRa], O. Gabber, L. Ramero, Foundations of Almost Ring Theory, arXiv:math/0409584

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe w v u

namespace TwoCategory

theorem exists_equivalence_of_quasiInverses {B : Type u} [Bicategory.{w, v} B] {a b : B}
    (f : a ⟶ b) (g h : b ⟶ a) (α : 𝟙 a ≅ f ≫ g) (β : h ≫ f ≅ 𝟙 b) :
    ∃ e : Bicategory.Equivalence a b, e.hom = f ∧ e.inv = g := by sorry

end TwoCategory
