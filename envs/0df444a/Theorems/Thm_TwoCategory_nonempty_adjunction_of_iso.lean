-- Prove2me | Theorems.Thm_TwoCategory_nonempty_adjunction_of_iso
-- name    : TwoCategory.nonempty_adjunction_of_iso
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:30.929846+00:00
-- url     : https://prove2.me/theorems/4e3da821-859a-4730-a795-5c7d112fd735
-- title:
--   Adjunctions in a bicategory transport along 2-isomorphisms of the two adjoints
-- statement:
--   In a bicategory, 1-morphisms 2-isomorphic to a pair of adjoint 1-morphisms are again adjoint.
--
--   Throughout, $\mathcal C$ is a bicategory (for instance a strict 2-category in the sense of Definition E.5.2.1 of the source). For 1-morphisms $f:A\to B$ and $g:B\to C$ the composite is written $g\circ f$, the identity 1-morphism of $A$ is $1_A$ (the source writes $\bullet_A$), and a *2-isomorphism* is an invertible 2-morphism. Following Definition E.5.2.3(3) of the source, a 1-morphism $g:B\to A$ is *right adjoint* to $f:A\to B$ (and $(f,g)$ is an *adjunction*) if there are 2-morphisms $\eta:1_A\Rightarrow g\circ f$ and $\varepsilon:f\circ g\Rightarrow 1_B$ satisfying the triangle identities
--
--   $$(\varepsilon\star 1_f)\odot(1_f\star\eta)=1_f,\qquad (1_g\star\varepsilon)\odot(\eta\star 1_g)=1_g$$
--
--   (read modulo the unit and associativity constraints).
--
--   **Statement.** Let $(f,g)$ be an adjunction in $\mathcal C$, with $f:A\to B$ and $g:B\to A$, and let $\alpha:f\Rightarrow f'$ and $\beta:g\Rightarrow g'$ be 2-isomorphisms. Then $(f',g')$ is an adjunction: $g'$ is right adjoint to $f'$.
--
--   The statement makes adjointness a property of 2-isomorphism classes of 1-morphisms; in the source it accompanies the uniqueness of right adjoints up to 2-isomorphism (Remark E.5.2.5(4); in Mathlib it follows from `CategoryTheory.Bicategory.conjugateIsoEquiv` applied to the identity 2-isomorphism of $f$).
--
--   **Formalization Note.** Lean composes in diagrammatic order (`f ≫ g` is $g\circ f$). `Bicategory.Adjunction f g` is Mathlib's structure of adjunctions in a bicategory (`unit : 𝟙 a ⟶ f ≫ g`, `counit : g ≫ f ⟶ 𝟙 b` and the two triangle identities, with unitors and associators made explicit); the conclusion is the existence of such a structure for `f'`, `g'`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 900-902, Remark E.5.2.5(5) (with Definition E.5.2.3(3)); classical reference: the paper cites [GR, Ch. 2, Rem. 2.1.4] at this spot; the entry printed under the key [GR] in the paper's bibliography is an unrelated article (P. Górka, E. G. Reyes, Sobolev spaces on locally compact abelian groups), and the work meant is presumably the bibliography entry [GRa], O. Gabber, L. Ramero, Foundations of Almost Ring Theory, arXiv:math/0409584

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe w v u

namespace TwoCategory

theorem nonempty_adjunction_of_iso {B : Type u} [Bicategory.{w, v} B] {a b : B}
    {f f' : a ⟶ b} {g g' : b ⟶ a} (adj : Bicategory.Adjunction f g) (α : f ≅ f') (β : g ≅ g') :
    Nonempty (Bicategory.Adjunction f' g') := by sorry

end TwoCategory
