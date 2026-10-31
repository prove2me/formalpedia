-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P59_strictLocalization_unique
-- name    : QAlgorithms.Papers.Independent.Intake100.P59.strictLocalization_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:03:55.533486+00:00
-- url     : https://prove2.me/theorems/a08628d1-2f58-4bb0-8370-82a1d0a584a5
-- title:
--   Uniqueness of strict localization over the original category
-- statement:
--   Let $C,D,D^{\prime}$ be categories in fixed compatible universes, and let $W$ be any class of arrows of $C$. Suppose $L:C\to D$ and $L^{\prime}:C\to D^{\prime}$ invert $W$ and satisfy strict unique factorization: every functor $\Phi:C\to E$ inverting $W$ factors as $\Phi=\Psi\circ L$ in exactly one way, and likewise through $L^{\prime}$, for every target category $E$ in those universes. There is a unique functor $T:D\to D^{\prime}$ commuting with localization and admitting a strict inverse $S:D^{\prime}\to D$ over $C$:
--
--   $$
--   T\circ L=L^{\prime},\quad S\circ L^{\prime}=L,\quad S\circ T=\mathrm{id}_D,\quad T\circ S=\mathrm{id}_{D^{\prime}}.
--   $$
--
--   Thus uniqueness is a unique compatible isomorphism, rather than equality of category types.
-- source:
--   Orbifolds as stacks?, arXiv:0806.4160v2, PDF p. 9, Lemma 3.12

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P59

namespace QAlgorithms.Papers.Independent.Intake100.P59

open CategoryTheory

universe u v uC vC uD vD uE vE

/-- Lemma 3.12, PDF p.9: strict localizations are uniquely isomorphic over C.
The hypotheses quantify strict unique factorization over every target category
in the fixed compatible universes. The inverse equalities are literal equalities
of functors, not just natural isomorphisms. -/
theorem strictLocalization_unique
    {C D D2 : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} D2]
    (W : MorphismProperty C) (L : C ⥤ D) (L2 : C ⥤ D2)
    (hL : ∀ (E : Type u) [Category.{v} E],
      Nonempty (Localization.StrictUniversalPropertyFixedTarget L W E))
    (hL2 : ∀ (E : Type u) [Category.{v} E],
      Nonempty (Localization.StrictUniversalPropertyFixedTarget L2 W E)) :
    ∃! F : D ⥤ D2, L ⋙ F = L2 ∧
      ∃ G : D2 ⥤ D, L2 ⋙ G = L ∧ F ⋙ G = 𝟭 D ∧ G ⋙ F = 𝟭 D2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P59
