-- Prove2me | Theorems.Thm_RSF_six_functor_formalism
-- name    : RSF.six_functor_formalism
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-23T03:14:59.059714+00:00
-- url     : https://prove2.me/theorems/c958e184-6861-4ab0-a6df-1775874d3679
-- title:
--   The six functors satisfy the formalism (Theorem 1.2.4)
-- statement:
--   Theorem 1.2.4 of the thesis: the assignment of the sheaf categories to the spaces, together with the six functors - tensor, internal hom, pullback, pushforward, lower shriek, upper shriek - satisfies the compatibilities of a six-functor formalism: (i) functoriality - the pullback of a composite is the composite of the pullbacks in reverse order, the pushforward of a composite is the composite of the pushforwards, and the two shriek functors are functorial on the bdcs maps; (ii) the special cases - upper shriek agrees with pullback along etale maps, lower shriek with pushforward along proper maps; (iii) the projection formula f_!(N tensor f^*M) = f_!N tensor M for bdcs f; and (iv) proper base change along cartesian squares with bdcs vertical maps. The isomorphisms of the paper are encoded as equalities of the bundled operations.
--
--   **Formalization Note** The world is abstract interface data; constructing it for the solid almost module categories of the thesis and establishing the compatibilities is the proposed work.
-- source:
--   L. Mann, A p-Adic 6-Functor Formalism in Rigid-Analytic Geometry, arXiv:2206.02022 (2022), Theorem 1.2.4 (proved as Corollary 3.6.15).

import Mathlib
import Definitions.Def_RSF_cat
import Definitions.Def_RSF_geo

namespace RSF

/-!  Theorem 1.2.4 of the thesis: the assignment of the sheaf categories to
the spaces, together with the six functors, satisfies the compatibilities of
a 6-functor formalism: functoriality of the pullback and pushforward and,
for bdcs maps, of the two shriek functors; the special cases - upper shriek
agrees with pullback along etale maps, lower shriek with pushforward along
proper maps; the projection formula for bdcs maps; and proper base change
along cartesian squares with bdcs vertical maps. The isomorphisms of the
paper are encoded as equalities of the bundled operations.  -/

theorem six_functor_formalism : ∀ w : SixFunctorWorld,
    (∀ (X Y Z : w.Space) (f : w.Map X Y) (g : w.Map Y Z) (M : w.C Z),
      w.pull X Z (w.compMap X Y Z f g) M = w.pull X Y f (w.pull Y Z g M)) ∧
    (∀ (X Y Z : w.Space) (f : w.Map X Y) (g : w.Map Y Z) (M : w.C X),
      w.push X Z (w.compMap X Y Z f g) M = w.push Y Z g (w.push X Y f M)) ∧
    (∀ (X Y Z : w.Space) (f : w.Map X Y) (g : w.Map Y Z)
        (hf : w.IsBdcs X Y f) (hg : w.IsBdcs Y Z g) (M : w.C X),
      w.lshriek X Z (w.compMap X Y Z f g) M = w.lshriek Y Z g (w.lshriek X Y f M)) ∧
    (∀ (X Y Z : w.Space) (f : w.Map X Y) (g : w.Map Y Z)
        (hf : w.IsBdcs X Y f) (hg : w.IsBdcs Y Z g) (M : w.C Z),
      w.ushriek X Z (w.compMap X Y Z f g) M = w.ushriek X Y f (w.ushriek Y Z g M)) ∧
    (∀ (X Y : w.Space) (f : w.Map X Y) (hf : w.IsEtale X Y f) (M : w.C Y),
      w.ushriek X Y f M = w.pull X Y f M) ∧
    (∀ (X Y : w.Space) (f : w.Map X Y) (hf : w.IsProper X Y f) (M : w.C X),
      w.lshriek X Y f M = w.push X Y f M) ∧
    (∀ (X Y : w.Space) (f : w.Map X Y) (hf : w.IsBdcs X Y f) (N : w.C X) (M : w.C Y),
      w.lshriek X Y f (w.tensor X N (w.pull X Y f M))
        = w.tensor Y (w.lshriek X Y f N) M) ∧
    (∀ (s : CartSquare w) (hf : w.IsBdcs s.Y s.X s.f) (N : w.C s.Y),
      w.pull s.X' s.X s.g (w.lshriek s.Y s.X s.f N)
        = w.lshriek s.Y' s.X' s.f' (w.pull s.Y' s.Y s.g' N)) := by
  sorry

end RSF
