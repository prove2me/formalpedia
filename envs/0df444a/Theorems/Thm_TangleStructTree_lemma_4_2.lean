-- Prove2me | Theorems.Thm_TangleStructTree_lemma_4_2
-- name    : TangleStructTree.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:37.34378+00:00
-- url     : https://prove2.me/theorems/9edeb5d8-91e4-47ea-853a-65126aca7674
-- title:
--   Lemma 4.2 — strongly efficient subsets of $\lfloor\beta_v\rfloor$ lie in $\beta_v$; $\beta_v$ is efficient
-- statement:
--   Let $v$ be a node of a thoroughly ordered separation tree $T$ on an ordered separation system $\vec S$. Then
--
--   1. every strongly efficient subset of $\lfloor\beta_v\rfloor$ (strongly efficient in $\lfloor\beta_v\rfloor$) is contained in $\beta_v$;
--   2. if $\beta_v$ is consistent, it is efficient in any partial orientation $\tau$ of $S$ that includes $\lfloor\beta_v\rfloor$.
--
--   Part 1 moves witnesses from $\mathcal F$ out of the closure onto the path, which is where richness is used in the existence proof; part 2 is the key step of the converse.
--
--   **Formalization Note** $T$ is not assumed consistent nor to be a tangle structure tree.
--
--   Differences from the source:
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: an order function S → ℝ extended to S⃗ by |s⃗| = |s⃖| = |s| → ord : E → ℝ with ord (x∗) = ord x (IsOrderFunction); reason: such maps are exactly the extensions of maps S → ℝ; same instances
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Lemma 4.2, p.8 (PDF 19)

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

/-- **Lemma 4.2** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.8 (PDF 19)). Let `v` be a node of
a thoroughly ordered separation tree `T` on `S⃗`. Then
(i) every strongly efficient subset of `⌊β_v⌋` is contained in `β_v`;
(ii) if `β_v` is consistent, it is efficient in any partial orientation `τ` of `S` that includes
`⌊β_v⌋`.

**Formalization Note** `T` need not be consistent nor a tangle structure tree; `ord` is the order
function of the ordered separation system. -/
theorem lemma_4_2 (ord : E → ℝ) (hord : IsOrderFunction ord) (T : SepTree E)
    (hT : T.ThoroughlyOrdered ord) (v : List E) (hv : v ∈ T.nodes) :
    (∀ σ : Set E, StronglyEfficient ord σ (sepClosure (labels v)) → σ ⊆ labels v) ∧
      (IsConsistent (labels v) → ∀ τ : Set E, IsPartialOrientation τ →
        sepClosure (labels v) ⊆ τ → Efficient ord (labels v) τ) := by sorry
end TangleStructTree
