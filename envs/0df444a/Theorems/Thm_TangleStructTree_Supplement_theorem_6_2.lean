-- Prove2me | Theorems.Thm_TangleStructTree_Supplement_theorem_6_2
-- name    : TangleStructTree.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:12:30.444207+00:00
-- url     : https://prove2.me/theorems/673c6aed-75a4-416b-9ada-3312741daa87
-- title:
--   Theorem 6.2 — properties of efficient ordered $\mathcal F$-tangle structure trees (corrected: efficiency in $\lfloor\beta_\ell\rfloor$ in (iii) and (v))
-- statement:
--   Let $\vec S$ be an ordered separation system, $\mathcal F$ any set, and $(T,r,\beta)$ an efficient ordered $\mathcal F$-tangle structure tree for $\vec S$. Then:
--
--   1. For every leaf $\ell$, $\beta_\ell$ is consistent. If $\beta_\ell$ has no subset in $\mathcal F$, then $\lfloor\beta_\ell\rfloor$ is a tangle of $S$, and every $\mathcal F$-tangle of $S$ arises in this way.
--   2. For every non-leaf node $v$: $\beta_v$ has no subset in $\mathcal F$; $s_v$ is not oriented by $\lfloor\beta_v\rfloor$; both orientations $\vec s$ of $s_v$ are minimal in $\beta_v\cup\{\vec s\}$; and $|s_v|=\max\{|s_u|:u\le_r v\}$.
--   3. For every orientation $\tau$ of $S$ there is a unique leaf $\ell$ with $\beta_\ell\subseteq\tau$. If $\tau$ is consistent, then $\lfloor\beta_\ell\rfloor\subseteq\tau$ and $\beta_\ell$ is efficient in $\lfloor\beta_\ell\rfloor$.
--   4. For every $\mathcal F$-tangle $\tau$ of $S$ there is a unique leaf $\ell$ with $\beta_\ell\subseteq\tau$; then $\tau=\lfloor\beta_\ell\rfloor$ and $\beta_\ell$ is efficient in $\tau$.
--   5. For every consistent orientation $\tau$ of $S$ that is not an $\mathcal F$-tangle, the set $\beta_\ell$ of (3) has a subset $\sigma\in\mathcal F$, and every such $\sigma$ is efficient in $\lfloor\beta_\ell\rfloor$.
--
--   The theorem says that the properties built into Theorem 6.1's trees hold for every efficient ordered tangle structure tree.
--
--   Differences from the source:
--   - correction: (iii) "β_ℓ is efficient in τ"; (v) "every such σ is efficient in τ" → (iii) β_ℓ is efficient in ⌊β_ℓ⌋; (v) every such σ is efficient in ⌊β_ℓ⌋; reason: both printed clauses are false: S⃗ = {r⃗, r⃖, s⃗, s⃖} with r⃗ < s⃗ (so s⃖ < r⃖) and no other relations, |r| = 0, |s| = 1, ℱ = {{s⃗}, {r⃗}} (standard); the tree splitting once on s, with leaves [s⃗] (forbidden) and [s⃖] (tangle leaf, ⌊{s⃖}⌋ = {s⃖, r⃖}), is an efficient, ordered, even irreducible ℱ-tangle structure tree; for the consistent orientation τ = {r⃗, s⃗}, the leaf with β_ℓ ⊆ τ is [s⃗], and s⃗ is eclipsed by r⃗ ∈ τ (checked in Lean, Solutions/verification). The proof of (iii) cites Lemma 4.2(ii), which needs a thoroughly ordered tree. Every other clause is as printed
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: an order function S → ℝ extended to S⃗ by |s⃗| = |s⃖| = |s| → ord : E → ℝ with ord (x∗) = ord x (IsOrderFunction); reason: such maps are exactly the extensions of maps S → ℝ; same instances
--   - encoding: both orientations s⃗ of s_v are minimal in β_v ∪ {s⃗} → for every child label x′ of v, no y ∈ β_v has y < x′; reason: x′ is never strictly below itself, so minimality in β_v ∪ {x′} is exactly this
--   - reading: (v) "not a tangle" → not an ℱ-tangle; reason: the tangles of the theorem are ℱ-tangles
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Theorem 6.2, pp.16–17 (PDF 27–28); = extended abstract Theorem 6.2, p.7

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_StronglyEfficient
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_Supplement_IsEfficientTree
import Definitions.Def_TangleStructTree_Supplement_IsOrderedTree

namespace TangleStructTree

namespace Supplement

open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- **Theorem 6.2** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version (Part I), p.16 (PDF 27); = extended abstract Theorem 6.2, p.7), corrected in two
efficiency clauses. Let `S⃗` be an ordered separation system. Every efficient ordered `ℱ`-tangle
structure tree `(T, r, β)` for `S⃗` has the following properties.
(i) For every leaf `ℓ` of `T`, the set `β_ℓ` is consistent in `S`. If `β_ℓ` has no subset in
`ℱ`, then `⌊β_ℓ⌋` is a tangle of `S`, and every `ℱ`-tangle of `S` arises in this way.
(ii) For every non-leaf node `v` of `T`, the set `β_v` has no subset in `ℱ`, and `s_v` is not
oriented by `⌊β_v⌋`. Both its orientations `s⃗ ∈ {s⃖_v, s⃗_v}` are minimal in `β_v ∪ {s⃗}`. Its order
`|s|` is maximal in `{|s_u| : u ≤_r v}`.
(iii) For every orientation `τ` of `S` there is a unique leaf `ℓ` of `T` such that `β_ℓ ⊆ τ`.
If `τ` is consistent, then `⌊β_ℓ⌋ ⊆ τ` and `β_ℓ` is efficient in `⌊β_ℓ⌋` (printed: "in `τ`").
(iv) For every `ℱ`-tangle `τ` of `S` there is a unique leaf `ℓ` of `T` such that `β_ℓ ⊆ τ`.
Then `τ = ⌊β_ℓ⌋`, and `β_ℓ` is efficient in the tangle `τ`.
(v) For every consistent orientation `τ` of `S` that is not a tangle, the set `β_ℓ` in (iii)
has a subset `σ` in `ℱ`. Every such `σ` is efficient in `⌊β_ℓ⌋` (printed: "in `τ`").

**Formalization Note**
1. Correction: the printed clauses "`β_ℓ` is efficient in `τ`" in (iii) and "every such `σ` is
   efficient in `τ`" in (v) are false. Counterexample: `S⃗ = {r⃗, r⃖, s⃗, s⃖}` with `r⃗ < s⃗` (so
   `s⃖ < r⃖`) and no other relations, `|r| = 0`, `|s| = 1`, `ℱ = {{s⃗}, {r⃗}}`; the tree splitting
   once on `s` is an efficient ordered `ℱ`-tangle structure tree, and for the consistent
   orientation `τ = {r⃗, s⃗}` its leaf `[s⃗] ⊆ τ` has `s⃗` eclipsed by `r⃗ ∈ τ`. The clauses are
   replaced by "efficient in `⌊β_ℓ⌋`"; every other clause is as printed.
2. Nodes are root-path label lists, newest first: `v` is a non-leaf iff some `x :: v` is a node,
   the child labels `x` are the orientations of `s_v`, `|s_v| = ord x`, and `u ≤_r v` is `u <:+ v`.
3. "Not a tangle" in (v) is "not an `ℱ`-tangle". No finiteness, richness or standardness is
   assumed (the source assumes none). -/
theorem theorem_6_2 (ord : E → ℝ) (hord : IsOrderFunction ord) (ℱ : Set (Set E))
    (T : SepTree E) (hT : T.IsTST ℱ) (heff : IsEfficientTree T ord) (hordT : IsOrderedTree T ord) :
    -- (i)
    (∀ ℓ : List E, T.IsLeaf ℓ → IsConsistent (labels ℓ) ∧
        (Avoids ℱ (labels ℓ) → IsTangle ℱ (sepClosure (labels ℓ)))) ∧
    (∀ τ : Set E, IsTangle ℱ τ →
        ∃ ℓ : List E, T.IsLeaf ℓ ∧ Avoids ℱ (labels ℓ) ∧ sepClosure (labels ℓ) = τ) ∧
    -- (ii)
    (∀ (v : List E) (x : E), x :: v ∈ T.nodes →
        Avoids ℱ (labels v) ∧ ¬ Orients (sepClosure (labels v)) x ∧
        (∀ x' : E, x' :: v ∈ T.nodes → ∀ y ∈ labels v, ¬ y < x') ∧
        (∀ (u : List E) (y : E), y :: u ∈ T.nodes → u <:+ v → ord y ≤ ord x)) ∧
    -- (iii)
    (∀ τ : Set E, IsOrientation τ →
        (∃! ℓ : List E, T.IsLeaf ℓ ∧ labels ℓ ⊆ τ) ∧
        (IsConsistent τ → ∀ ℓ : List E, T.IsLeaf ℓ → labels ℓ ⊆ τ →
          sepClosure (labels ℓ) ⊆ τ ∧ Efficient ord (labels ℓ) (sepClosure (labels ℓ)))) ∧
    -- (iv)
    (∀ τ : Set E, IsTangle ℱ τ →
        (∃! ℓ : List E, T.IsLeaf ℓ ∧ labels ℓ ⊆ τ) ∧
        (∀ ℓ : List E, T.IsLeaf ℓ → labels ℓ ⊆ τ →
          τ = sepClosure (labels ℓ) ∧ Efficient ord (labels ℓ) τ)) ∧
    -- (v)
    (∀ τ : Set E, IsOrientation τ → IsConsistent τ → ¬ IsTangle ℱ τ →
        ∀ ℓ : List E, T.IsLeaf ℓ → labels ℓ ⊆ τ →
          (∃ σ ∈ ℱ, σ ⊆ labels ℓ) ∧
          (∀ σ ∈ ℱ, σ ⊆ labels ℓ → Efficient ord σ (sepClosure (labels ℓ)))) := by sorry

end Supplement

end TangleStructTree
