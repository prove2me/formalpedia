-- Prove2me | Theorems.Thm_TangleStructTree_Supplement_theorem_6_3
-- name    : TangleStructTree.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:13:04.90688+00:00
-- url     : https://prove2.me/theorems/8747e024-788f-43c1-a720-781346cd807e
-- title:
--   Theorem 6.3 — the restriction $T|_k$ is a thoroughly ordered $\mathcal F$-tangle structure tree of $\vec S_k$ (corrected: $\mathcal F$ standard for $\vec S_k$)
-- statement:
--   Let $(T,r,\beta)$ be a thoroughly ordered $\mathcal F$-tangle structure tree of an ordered separation system $\vec S$, and let $k\in\mathbb R$. Assume that $\mathcal F$ is rich **and standard** for $\vec S_k=\{\vec s\in\vec S:|s|<k\}$. Let $T|_k$ be the subtree of $T$ formed by the edges $e$ with $|\beta(e)|<k$, with the restricted labelling. Then
--
--   $$T|_k\ \text{ is a thoroughly ordered } \mathcal F\text{-tangle structure tree of } \vec S_k .$$
--
--   So the tangle structure trees of all the $\vec S_k$ are found inside one tree for $\vec S$, nested in $k$.
--
--   Differences from the source:
--   - correction: ℱ rich for S⃗_k → ℱ rich and standard for S⃗_k (IsStandard (restrictFamily ord k ℱ)); reason: the printed statement is false: S⃗ = {s⃗, s⃖, r⃗, r⃖, x⃗, x⃖} with r⃗, r⃖ < s⃗ (so s⃖ < r⃗, r⃖) and x incomparable to all, |s| = 1, |r| = 2, |x| = 3, k = 3, ℱ = {{s⃖, x⃗}, {s⃖, x⃖}}; the tree splitting on s, then on r below s⃗ and on x below s⃖, then on x below [r^±, s⃗], is a thoroughly ordered ℱ-tangle structure tree of S⃗; ℱ read on S⃗_3 is empty, hence rich; but the leaf [s⃖] of T|_3 has closure {s⃖, r⃗, r⃖}, not a tangle, and avoids ℱ, so T|_3 is not an ℱ-tangle structure tree. The proof applies Lemma 4.5 in S⃗_k, which needs standardness there. Standard for S⃗ implies standard for S⃗_k, so the added hypothesis is the weakest that repairs the proof
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: an order function S → ℝ extended to S⃗ by |s⃗| = |s⃖| = |s| → ord : E → ℝ with ord (x∗) = ord x (IsOrderFunction); reason: such maps are exactly the extensions of maps S → ℝ; same instances
--   - encoding: S⃗_k = {s⃗ ∈ S⃗ : |s| < k} → the subtype Sk ord k = {x // ord x < k ∧ ord (x∗) < k} with the induced order, involution and order function; reason: for an order function both conditions say |s| < k, so it is the same set; the second makes the subtype closed under ∗ without a hypothesis
--   - encoding: ℱ on S⃗_k → restrictFamily ord k ℱ: the σ ⊆ S⃗_k with σ ∈ ℱ; reason: elements of ℱ not contained in S⃗_k are never subsets of orientations of S_k
--   - encoding: (T, r, β)|_k, the subtree of the edges of order < k → ∃ T′ : SepTree (Sk ord k) whose nodes are the label lists v with v.map val ∈ T.nodes, and T′ has the conclusion; reason: the subtree of edges of order < k rooted at r consists of the nodes all of whose root-path labels have order < k; asserting its existence keeps the statement from being vacuous
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Theorem 6.3, p.18 (PDF 29); definition of T|_k, pp.17–18 (PDF 28–29)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsStandard
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_IsRich
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_SepTree_ThoroughlyOrdered
import Definitions.Def_TangleStructTree_Supplement_Sk

namespace TangleStructTree

namespace Supplement

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- **Theorem 6.3** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version (Part I), p.18 (PDF 29)), corrected: `ℱ` also standard for `S⃗_k`. Let
`(T, r, β)` be a thoroughly ordered `ℱ`-tangle structure tree of `S⃗`. Let `k ∈ ℝ`, and assume that
`ℱ` is rich (and standard) for `S⃗_k`. Then `(T, r, β)|_k` is a thoroughly ordered `ℱ`-tangle
structure tree of `S⃗_k`.

**Formalization Note**
1. Correction: the hypothesis "`ℱ` is standard for `S⃗_k`" is added. Without it the statement is
   false: `S⃗ = {s⃗, s⃖, r⃗, r⃖, x⃗, x⃖}` with `r⃗, r⃖ < s⃗` (so `s⃖ < r⃗, r⃖`), `x` incomparable to all,
   `|s| = 1`, `|r| = 2`, `|x| = 3`, `k = 3`, `ℱ = {{s⃖, x⃗}, {s⃖, x⃖}}`. The thoroughly ordered tree
   splitting on `s`, then on `r` below `s⃗` and on `x` below `s⃖`, then on `x` below `{r^±, s⃗}`, is an
   `ℱ`-tangle structure tree of `S⃗`; `ℱ` read on `S⃗_3` is empty, hence rich for `S⃗_3`; but the
   leaf `[s⃖]` of `T|_3` is neither a tangle leaf nor forbidden. The paper's proof applies
   Lemma 4.5 in `S⃗_k`, which needs standardness there.
2. `S⃗_k` is the subtype `Sk ord k` (induced order, restricted involution, order `x ↦ ord x`);
   `ℱ` on `S⃗_k` is `restrictFamily ord k ℱ`, the elements of `ℱ` that are subsets of `S⃗_k`.
3. `T|_k`, the subtree of the edges of order `< k`, is the separation tree on `S⃗_k` whose nodes are
   the root-path label lists of `T` all of whose labels have order `< k`: the lists `v` over `S⃗_k`
   with `v.map Subtype.val ∈ T.nodes`. Its existence is part of the conclusion. -/
theorem theorem_6_3 (ord : E → ℝ) (hord : IsOrderFunction ord) (ℱ : Set (Set E))
    (T : SepTree E) (hTO : T.ThoroughlyOrdered ord) (hT : T.IsTST ℱ) (k : ℝ)
    (hrich : IsRich (fun x : Sk ord k => ord x.1) (restrictFamily ord k ℱ))
    (hstd : IsStandard (restrictFamily ord k ℱ)) :
    ∃ T' : SepTree (Sk ord k),
      (∀ v : List (Sk ord k), v ∈ T'.nodes ↔ v.map Subtype.val ∈ T.nodes) ∧
      T'.ThoroughlyOrdered (fun x => ord x.1) ∧ T'.IsTST (restrictFamily ord k ℱ) := by sorry

end Supplement

end TangleStructTree
