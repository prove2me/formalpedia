-- Prove2me | Theorems.Thm_TwoCategory_exists_equivalence_iff_of_iso
-- name    : TwoCategory.exists_equivalence_iff_of_iso
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:32.261585+00:00
-- url     : https://prove2.me/theorems/3788c6d0-be5f-4498-9988-11ea275eb96d
-- title:
--   Being an equivalence in a bicategory is invariant under 2-isomorphism of 1-morphisms
-- statement:
--   The property of being an equivalence in a bicategory propagates along 2-isomorphisms between 1-morphisms.
--
--   Throughout, $\mathcal C$ is a bicategory (for instance a strict 2-category in the sense of Definition E.5.2.1 of the source). For 1-morphisms $f:A\to B$ and $g:B\to C$ the composite is written $g\circ f$, the identity 1-morphism of $A$ is $1_A$ (the source writes $\bullet_A$), and a *2-isomorphism* is an invertible 2-morphism. Following Definition E.5.2.3(1) of the source, a 1-morphism $f:A\to B$ is an *equivalence* if there are 1-morphisms $g,h:B\to A$ and 2-isomorphisms $\alpha:1_A\Rightarrow g\circ f$ and $\beta:f\circ h\Rightarrow 1_B$. By the companion statement `TwoCategory.exists_equivalence_of_quasiInverses` this holds if and only if $f$ is the 1-morphism underlying an *adjoint equivalence* $(f,g,\eta,\varepsilon)$: a 1-morphism $g:B\to A$ with 2-isomorphisms $\eta:1_A\Rightarrow g\circ f$, $\varepsilon:f\circ g\Rightarrow 1_B$ satisfying the triangle identity.
--
--   **Statement.** Let $f,g:A\to B$ be two 1-morphisms of $\mathcal C$ and let $\alpha:f\Rightarrow g$ be a 2-isomorphism. Then
--
--   $$f\ \text{is an equivalence}\iff g\ \text{is an equivalence}.$$
--
--   It makes being an equivalence a property of the 2-isomorphism class of a 1-morphism; the source recalls it, together with closure under composition (Remark E.5.2.5(2)), among the basic properties of equivalences before the 2-categories of groupoids, of fibered categories and of stacks of Appendix E are introduced.
--
--   **Formalization Note.** Lean composes in diagrammatic order: `f ≫ g` is $g\circ f$. `Bicategory.Equivalence a b` is Mathlib's structure of adjoint equivalences between objects `a`, `b` of a bicategory (fields `hom : a ⟶ b`, `inv : b ⟶ a`, `unit : 𝟙 a ≅ hom ≫ inv`, `counit : inv ≫ hom ≅ 𝟙 b` and the left triangle identity); "$f$ is an equivalence" is rendered as `∃ e : Bicategory.Equivalence a b, e.hom = f`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 901, Remark E.5.2.5(3); classical reference: the paper cites [GR, Ch. 2, Rem. 2.1.4] at this spot; the entry printed under the key [GR] in the paper's bibliography is an unrelated article (P. Górka, E. G. Reyes, Sobolev spaces on locally compact abelian groups), and the work meant is presumably the bibliography entry [GRa], O. Gabber, L. Ramero, Foundations of Almost Ring Theory, arXiv:math/0409584

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe w v u

namespace TwoCategory

theorem exists_equivalence_iff_of_iso {B : Type u} [Bicategory.{w, v} B] {a b : B}
    {f g : a ⟶ b} (α : f ≅ g) :
    (∃ e : Bicategory.Equivalence a b, e.hom = f) ↔
      (∃ e : Bicategory.Equivalence a b, e.hom = g) := by sorry

end TwoCategory
