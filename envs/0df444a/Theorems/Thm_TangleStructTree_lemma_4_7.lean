-- Prove2me | Theorems.Thm_TangleStructTree_lemma_4_7
-- name    : TangleStructTree.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:56:31.385483+00:00
-- url     : https://prove2.me/theorems/ef52dd7c-6d47-4514-94d0-38263c42dd72
-- title:
--   Lemma 4.7 — for injective order functions, a thoroughly ordered $\mathcal F$-tangle structure tree forces $\mathcal F$ to be rich
-- statement:
--   Let $\vec S$ be a separation system with an order function that is injective on $S$, and let $\mathcal F$ be any set. If there exists a thoroughly ordered $\mathcal F$-tangle structure tree $T$ of $\vec S$, then $\mathcal F$ is rich for $\vec S$.
--
--   So richness is the weakest condition on $\mathcal F$ under which thoroughly ordered tangle structure trees exist.
--
--   Differences from the source:
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: an order function S → ℝ extended to S⃗ by |s⃗| = |s⃖| = |s| → ord : E → ℝ with ord (x∗) = ord x (IsOrderFunction); reason: such maps are exactly the extensions of maps S → ℝ; same instances
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Lemma 4.7, p.11 (PDF 22)

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

/-- **Lemma 4.7** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.11 (PDF 22)). Let `S⃗` be a
separation system with an injective order function on `S`, and let `ℱ` be any set. If there exists
a thoroughly ordered `ℱ`-tangle structure tree `T` of `S⃗`, then `ℱ` is rich for `S⃗`. -/
theorem lemma_4_7 (ord : E → ℝ) (hord : IsOrderFunction ord) (hinj : OrderInjective ord)
    (ℱ : Set (Set E)) (hT : ∃ T : SepTree E, T.ThoroughlyOrdered ord ∧ T.IsTST ℱ) :
    IsRich ord ℱ := by sorry
end TangleStructTree
