-- Prove2me | Theorems.Thm_TwoCategory_exists_equivalence_comp
-- name    : TwoCategory.exists_equivalence_comp
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:27.61454+00:00
-- url     : https://prove2.me/theorems/9742e6da-fb35-4f09-9a7e-4a378df3f545
-- title:
--   Equivalences in a bicategory are closed under composition
-- statement:
--   The composite of two equivalences in a bicategory is an equivalence.
--
--   Throughout, $\mathcal C$ is a bicategory (for instance a strict 2-category in the sense of Definition E.5.2.1 of the source). For 1-morphisms $f:A\to B$ and $g:B\to C$ the composite is written $g\circ f$, the identity 1-morphism of $A$ is $1_A$ (the source writes $\bullet_A$), and a *2-isomorphism* is an invertible 2-morphism. Following Definition E.5.2.3(1) of the source, a 1-morphism $f:A\to B$ is an *equivalence* if there are 1-morphisms $g,h:B\to A$ and 2-isomorphisms $\alpha:1_A\Rightarrow g\circ f$ and $\beta:f\circ h\Rightarrow 1_B$. By the companion statement `TwoCategory.exists_equivalence_of_quasiInverses` this holds if and only if $f$ is the 1-morphism underlying an *adjoint equivalence* $(f,g,\eta,\varepsilon)$: a 1-morphism $g:B\to A$ with 2-isomorphisms $\eta:1_A\Rightarrow g\circ f$, $\varepsilon:f\circ g\Rightarrow 1_B$ satisfying the triangle identity.
--
--   **Statement.** Let $f:A\to B$ and $g:B\to C$ be equivalences in $\mathcal C$. Then the composite
--
--   $$g\circ f:A\to C$$
--
--   is an equivalence in $\mathcal C$.
--
--   This is one of the basic permanence properties of equivalences recalled in the source before the 2-categories of groupoids, of fibered categories and of stacks are introduced; it is what makes "equivalent" a transitive relation on the objects of a 2-category.
--
--   **Formalization Note.** Lean composes in diagrammatic order: `f ≫ g` is $g\circ f$. `Bicategory.Equivalence a b` is Mathlib's structure of adjoint equivalences between objects `a`, `b` of a bicategory (fields `hom : a ⟶ b`, `inv : b ⟶ a`, `unit : 𝟙 a ≅ hom ≫ inv`, `counit : inv ≫ hom ≅ 𝟙 b` and the left triangle identity); "$f$ is an equivalence" is rendered as `∃ e : Bicategory.Equivalence a b, e.hom = f`. The two given equivalences are adjoint equivalences `e₁ : Bicategory.Equivalence a b`, `e₂ : Bicategory.Equivalence b c` with $f$ = `e₁.hom`, $g$ = `e₂.hom`, and the conclusion provides an adjoint equivalence whose underlying 1-morphism is `e₁.hom ≫ e₂.hom` $=g\circ f$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 901, Remark E.5.2.5(2); classical reference: the paper cites [GR, Ch. 2, Rem. 2.1.4] at this spot; the entry printed under the key [GR] in the paper's bibliography is an unrelated article (P. Górka, E. G. Reyes, Sobolev spaces on locally compact abelian groups), and the work meant is presumably the bibliography entry [GRa], O. Gabber, L. Ramero, Foundations of Almost Ring Theory, arXiv:math/0409584

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe w v u

namespace TwoCategory

theorem exists_equivalence_comp {B : Type u} [Bicategory.{w, v} B] {a b c : B}
    (e₁ : Bicategory.Equivalence a b) (e₂ : Bicategory.Equivalence b c) :
    ∃ e : Bicategory.Equivalence a c, e.hom = e₁.hom ≫ e₂.hom := by sorry

end TwoCategory
