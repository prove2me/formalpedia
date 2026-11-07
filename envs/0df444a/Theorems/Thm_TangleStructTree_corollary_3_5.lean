-- Prove2me | Theorems.Thm_TangleStructTree_corollary_3_5
-- name    : TangleStructTree.corollary_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:34.011249+00:00
-- url     : https://prove2.me/theorems/09484e7d-928c-4062-b1e4-23dc7c9074dc
-- title:
--   Corollary 3.5 — at most $2^{|S|}$ leaves and fewer than $2^{|S|+1}$ nodes
-- statement:
--   Let $\vec S$ be a finite separation system and let $|S|$ be the number of its unoriented separations. Every separation tree on $\vec S$ has at most $2^{|S|}$ leaves and fewer than $2^{|S|+1}$ nodes:
--   $$
--   \#\{\text{leaves}\}\le 2^{|S|},\qquad |V(T)|<2^{|S|+1}.
--   $$
--
--   The bound is what makes the iterative construction of a thoroughly ordered tangle structure tree terminate.
--
--   Differences from the source:
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: separation trees on S⃗ (no finiteness stated) → [Finite E], with |S| = (Unoriented E).ncard; reason: for infinite S the bounds 2^{|S|} and 2^{|S|+1} are infinite cardinals and the claim about finite trees holds trivially; the finite case is the whole content
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Corollary 3.5, p.7 (PDF 18)

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

/-- **Corollary 3.5** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.7 (PDF 18)). Separation
trees on `S⃗` have at most `2^{|S|}` leaves and fewer than `2^{|S|+1}` nodes.

**Formalization Note** `|S|` is the number of unoriented separations, `(Unoriented E).ncard`. `S⃗`
is assumed finite: for infinite `S` the bounds are infinite cardinals and the claim about finite
trees holds trivially. -/
theorem corollary_3_5 [Finite E] (T : SepTree E) :
    {ℓ : List E | T.IsLeaf ℓ}.ncard ≤ 2 ^ (Unoriented E).ncard ∧
      T.nodes.card < 2 ^ ((Unoriented E).ncard + 1) := by sorry
end TangleStructTree
