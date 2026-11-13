-- Prove2me | Theorems.Thm_TangleStructTree_lemma_3_2
-- name    : TangleStructTree.lemma_3_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:55:35.745824+00:00
-- url     : https://prove2.me/theorems/1b4a50bb-b012-4744-b49f-f80b9d43060e
-- title:
--   Lemma 3.2 — every orientation of $S$ contains $\beta_\ell$ for a unique leaf $\ell$
-- statement:
--   Let $(T,r,\beta)$ be a separation tree on a separation system $\vec S$. Every orientation $\tau$ of $S$ contains $\beta_\ell$ as a subset for a unique leaf $\ell$ of $T$:
--   $$
--   \exists!\,\ell\ \text{leaf of } T:\quad \beta_\ell\subseteq\tau .
--   $$
--
--   So the leaves of a separation tree partition the orientations of $S$; this is how a tangle structure tree locates each tangle.
--
--   Differences from the source:
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Lemma 3.2, p.6 (PDF 17)

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

/-- **Lemma 3.2** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.6 (PDF 17)). Let `(T, r, β)` be
a separation tree on `S⃗`. Every orientation `τ` of `S` contains `β_ℓ` as a subset for some unique
leaf `ℓ ∈ V(T)`.

**Formalization Note** Nodes are recorded by their root-path label lists (see `SepTree`); `β_ℓ` is
`labels ℓ`. -/
theorem lemma_3_2 (T : SepTree E) (τ : Set E) (hτ : IsOrientation τ) :
    ∃! ℓ : List E, T.IsLeaf ℓ ∧ labels ℓ ⊆ τ := by sorry
end TangleStructTree
