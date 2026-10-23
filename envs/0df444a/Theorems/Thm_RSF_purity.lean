-- Prove2me | Theorems.Thm_RSF_purity
-- name    : RSF.purity
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-23T03:15:35.621502+00:00
-- url     : https://prove2.me/theorems/2abe5d3f-d1e8-4e5a-b86e-a18f2def04ce
-- title:
--   Purity: upper shriek as a twist of pullback (Theorem 1.2.5 (i))
-- statement:
--   Theorem 1.2.5 (i) of the thesis: for a bdcs and p-cohomologically smooth map f, the natural morphism from the tensor of the upper shriek of the structure sheaf with the pullback to the upper shriek functor is an isomorphism, and the upper shriek of the structure sheaf is invertible for the tensor product. Together with the proper special case of the formalism this is the input from which the trace map of Poincare duality is built.
--
--   **Formalization Note** The world is abstract interface data; the isomorphism is encoded as an equality of the bundled operations applied to objects.
-- source:
--   L. Mann, A p-Adic 6-Functor Formalism in Rigid-Analytic Geometry, arXiv:2206.02022 (2022), Theorem 1.2.5 (i) (proved as Proposition 3.8.4).

import Mathlib
import Definitions.Def_RSF_cat
import Definitions.Def_RSF_geo

namespace RSF

/-!  Theorem 1.2.5 (i) of the thesis: purity. For a bdcs and
p-cohomologically smooth map, upper shriek is the tensor product of the
upper shriek of the structure sheaf with the pullback, and the upper shriek
of the structure sheaf is invertible for the tensor product. Together with
the special case that lower shriek agrees with pushforward along proper
maps, this is the formal input from which Poincare duality follows.  -/

theorem purity : ∀ (w : SixFunctorWorld) (X Y : w.Space) (f : w.Map Y X),
    w.IsBdcs Y X f → w.IsPCohSmooth Y X f →
    (∀ M : w.C X,
      w.ushriek Y X f M = w.tensor Y (w.ushriek Y X f (w.unit X)) (w.pull Y X f M)) ∧
    IsInvertible w Y (w.ushriek Y X f (w.unit X)) := by
  sorry

end RSF
