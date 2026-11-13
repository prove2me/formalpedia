-- Prove2me | Theorems.Thm_TangleStructTree_theorem_4_6
-- name    : TangleStructTree.theorem_4_6
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:55:48.192013+00:00
-- url     : https://prove2.me/theorems/028e780c-71bc-49fc-9b0c-f75af01c40cd
-- title:
--   Theorem 4.6 — rich and standard $\mathcal F$ admit a thoroughly ordered $\mathcal F$-tangle structure tree (corrected: finite separation system)
-- statement:
--   Let $\vec S$ be a finite ordered separation system, and let $\mathcal F$ be a set that is rich and standard for $\vec S$. Then there exists a thoroughly ordered $\mathcal F$-tangle structure tree of $\vec S$.
--
--   This is the existence half of the paper's main result: one tree, built by branching on separations in increasing order, displays every $\mathcal F$-tangle at a leaf and certifies every non-tangle by an element of $\mathcal F$ on a root–leaf path.
--
--   Differences from the source:
--   - correction: any (ordered) separation system S⃗ → [Finite E]; reason: the statement is false for infinite S⃗: take S⃗ = {s⃗_n, s⃖_n : n ∈ ℕ} with the trivial order (x ≤ y iff x = y), ∗ swapping s⃗_n and s⃖_n, all orders 0 and ℱ = ∅; ℱ is standard (nothing is trivial) and rich (nothing has a subset in ∅); an ℱ-tangle structure tree has no forbidden leaf, so it has a tangle leaf ℓ, but ⌊β_ℓ⌋ = β_ℓ is finite and orients only finitely many s_n. The paper's proof uses exactly finiteness (journal version p.7: paths have length at most |S|; p.10: termination by Corollary 3.5)
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: an order function S → ℝ extended to S⃗ by |s⃗| = |s⃖| = |s| → ord : E → ℝ with ord (x∗) = ord x (IsOrderFunction); reason: such maps are exactly the extensions of maps S → ℝ; same instances
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Theorem 4.6, p.10 (PDF 21)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_IsTrivial
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_IsStandard
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_OrderInjective
import Definitions.Def_TangleStructTree_StronglyEfficient
import Definitions.Def_TangleStructTree_IsRich
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_Consistent
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_SepTree_ThoroughlyOrdered

namespace TangleStructTree

open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- **Theorem 4.6** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.10 (PDF 21)), corrected: finite
separation system. Let `S⃗` be an ordered separation system, and let `ℱ` be a set that is rich and
standard for `S⃗`. Then there exists a thoroughly ordered `ℱ`-tangle structure tree of `S⃗`.

**Formalization Note** `[Finite E]` is a correction: the paper's proof uses that `S` is finite
("the length of any path from the root to a leaf is at most |S|", p.7; termination via Corollary
3.5, p.10), and the statement fails for infinite `S` (`S⃗ = {s⃗_n, s⃖_n : n ∈ ℕ}` with the trivial
order, all orders `0`, `ℱ = ∅`: a finite tree's leaf closure orients only finitely many `s_n`). -/
theorem theorem_4_6 [Finite E] (ord : E → ℝ) (hord : IsOrderFunction ord) (ℱ : Set (Set E))
    (hrich : IsRich ord ℱ) (hstd : IsStandard ℱ) :
    ∃ T : SepTree E, T.ThoroughlyOrdered ord ∧ T.IsTST ℱ := by sorry
end TangleStructTree
