-- Prove2me | Theorems.Thm_Subgroup_thompsonJ_ne_bot
-- name    : Subgroup.thompsonJ_ne_bot
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T04:47:55.323203+00:00
-- url     : https://prove2.me/theorems/1cf74fc6-7059-494e-b06a-5a755b044999
-- title:
--   The Thompson subgroup $J(P)$ of a nontrivial finite $p$-group is nontrivial
-- statement:
--   Let $G$ be a finite group, let $p$ be a prime, and let $P \le G$ be a nontrivial $p$-subgroup. Write $\mathcal{E}(P)$ for the set of elementary abelian $p$-subgroups $E \le P$ whose order is maximal among the orders of all elementary abelian $p$-subgroups of $P$, and let
--
--   $$J(P) \;=\; \bigl\langle E \;:\; E \in \mathcal{E}(P) \bigr\rangle$$
--
--   be the Thompson subgroup of $P$ (Isaacs, *Finite Group Theory*, Chapter 7). Then
--
--   $$J(P) \neq 1 .$$
--
--   Indeed, by Cauchy's theorem $P$ contains an element of order $p$, which generates an elementary abelian subgroup of order $p$; so the members of $\mathcal{E}(P)$ have order at least $p > 1$, and $J(P)$ contains them. The fact is used in Thompson's normal $p$-complement theorem (Isaacs, Chapter 7) and in Thompson's theorem that Frobenius kernels are nilpotent (Isaacs, Chapter 6).
--
--   **Formalization Note** $J(P)$ is `thompsonJ P p`, the supremum in `Subgroup G` of the members of `maxElemAbelianIn P p`; being a $p$-group is `IsPGroup p ↥P`, and nontriviality is `P ≠ ⊥`. The theorem lives in the namespace `Subgroup`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/ThompsonSubgroup.lean#L152-L207

import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas

namespace Subgroup

variable {G : Type*} [Group G]

theorem thompsonJ_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP_pgroup : IsPGroup p ↥P) (hP_ne_bot : P ≠ ⊥) :
    thompsonJ P p ≠ ⊥ := by sorry

end Subgroup
