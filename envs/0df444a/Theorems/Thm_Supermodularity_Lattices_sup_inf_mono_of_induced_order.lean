-- Prove2me | Theorems.Thm_Supermodularity_Lattices_sup_inf_mono_of_induced_order
-- name    : Supermodularity.Lattices.sup_inf_mono_of_induced_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:23:37.885824+00:00
-- url     : https://prove2.me/theorems/259a03bf-5b97-4b95-81f5-f7cc72313d14
-- title:
--   Lemma 2.4.2 - supremum and infimum are monotone under the induced set ordering
-- statement:
--   Let $X$ be a lattice and let $X', X'' \subseteq X$ be nonempty sets with
--   $X' \sqsubseteq X''$ in the induced set ordering (see `InducedSetOrder`). Then:
--
--   1. If $\sup_X X'$ and $\sup_X X''$ both exist (as least upper bounds in $X$), then
--      $\sup_X X' \preceq \sup_X X''$.
--   2. If $\inf_X X'$ and $\inf_X X''$ both exist (as greatest lower bounds in $X$), then
--      $\inf_X X' \preceq \inf_X X''$.
--
--   This is Lemma 2.4.2: the induced set ordering is compatible with taking suprema and
--   infima, whenever those exist. It is the key technical tool used to show that an
--   increasing correspondence's greatest (or least) selection is itself increasing, and
--   it drives the construction of the greatest and least fixed points in Theorem 2.5.1
--   and Theorem 2.5.2.
--
--   **Formalization Note** Each of the two conclusions only requires the existence of
--   the relevant suprema (respectively infima) for $X'$ and $X''$, encoded via
--   Mathlib's `IsLUB`/`IsGLB`; the two conjuncts do not require both a supremum and an
--   infimum to exist simultaneously, matching the book's own presentation of the sup and
--   inf statements as parallel, independently-applicable halves of the same lemma.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 36, Lemma 2.4.2

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace Supermodularity.Lattices

theorem sup_inf_mono_of_induced_order {X : Type*} [Lattice X] {X' X'' : Set X}
    (hX' : X'.Nonempty) (hX'' : X''.Nonempty) (hle : InducedSetOrder X' X'') :
    (∀ ⦃s : X⦄, IsLUB X' s → ∀ ⦃s' : X⦄, IsLUB X'' s' → s ≤ s') ∧
      (∀ ⦃i : X⦄, IsGLB X' i → ∀ ⦃i' : X⦄, IsGLB X'' i' → i ≤ i') := by sorry

end Supermodularity.Lattices
