-- Prove2me | Theorems.Thm_TangleStructTree_corollary_3_4
-- name    : TangleStructTree.corollary_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:28.442699+00:00
-- url     : https://prove2.me/theorems/b4932561-8f2f-42dc-83fe-52ab641b065b
-- title:
--   Corollary 3.4 — $s_v$ is not oriented by $\lfloor\beta_v\rfloor$
-- statement:
--   Let $(T,r,\beta)$ be a consistent separation tree on a separation system $\vec S$ and let $v$ be a non-leaf node with separation $s_v$. Then
--   $$
--   \{\vec s_v,\overleftarrow{s}_v\}\cap\lfloor\beta_v\rfloor=\emptyset ,
--   $$
--   that is, $s_v$ is not oriented by $\lfloor\beta_v\rfloor$.
--
--   Consistent separation trees therefore store orientations economically: no separation labels an edge below a node whose path already forces its orientation.
--
--   Differences from the source:
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Corollary 3.4, p.6 (PDF 17)

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

/-- **Corollary 3.4** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.6 (PDF 17)). For every
consistent separation tree and non-leaf node `v` we have `{s⃗_v, s⃖_v} ∩ ⌊β_v⌋ = ∅`. That is, `s_v`
is not oriented by `⌊β_v⌋`.

**Formalization Note** `x` is the label of an edge from `v` to a child, so `{x, x∗} = {s⃗_v, s⃖_v}`. -/
theorem corollary_3_4 (T : SepTree E) (hT : T.Consistent) (v : List E) (x : E)
    (hx : x :: v ∈ T.nodes) :
    ({x, rev x} : Set E) ∩ sepClosure (labels v) = ∅ ∧ ¬ Orients (sepClosure (labels v)) x := by sorry
end TangleStructTree
