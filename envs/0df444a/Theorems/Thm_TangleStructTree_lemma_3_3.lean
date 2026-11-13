-- Prove2me | Theorems.Thm_TangleStructTree_lemma_3_3
-- name    : TangleStructTree.lemma_3_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:55:26.162208+00:00
-- url     : https://prove2.me/theorems/dd0da5b7-baa9-41af-8274-33975fa7995d
-- title:
--   Lemma 3.3 — $\vec s_v$ and $\overleftarrow{s}_v$ are minimal over $\beta_v$
-- statement:
--   Let $(T,r,\beta)$ be a consistent separation tree on a separation system $\vec S$, and let $v$ be a non-leaf node of $T$ with separation $s_v$. Then $\vec s_v$ is $\le$-minimal in $\beta_v\cup\{\vec s_v\}$ and $\overleftarrow{s}_v$ is $\le$-minimal in $\beta_v\cup\{\overleftarrow{s}_v\}$; that is, no $\vec r\in\beta_v$ satisfies $\vec r<\vec s_v$, and none satisfies $\vec r<\overleftarrow{s}_v$.
--
--   The lemma is the step from consistency of the tree to the fact that $s_v$ is not already decided by $\lfloor\beta_v\rfloor$.
--
--   **Formalization Note** The orientations of $s_v$ are the labels $x$ of the edges from $v$ to its children; the statement is made for each of them.
--
--   Differences from the source:
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Lemma 3.3, p.6 (PDF 17)

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

/-- **Lemma 3.3** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.6 (PDF 17)). Let `(T, r, β)` be
a consistent separation tree on `S⃗`, and let `v` be a non-leaf node of `T`. Then `s⃗_v` and `s⃖_v`
are `≤`-minimal in `β_v ∪ {s⃗_v}` and in `β_v ∪ {s⃖_v}`, respectively.

**Formalization Note** The orientations of `s_v` are the labels `x` of the edges from `v` to its
children (the nodes `x :: v`); `x` is `≤`-minimal in `β_v ∪ {x}` iff no `y ∈ β_v` has `y < x`. -/
theorem lemma_3_3 (T : SepTree E) (hT : T.Consistent) (v : List E) (x : E)
    (hx : x :: v ∈ T.nodes) :
    ∀ y ∈ labels v, ¬ y < x := by sorry
end TangleStructTree
