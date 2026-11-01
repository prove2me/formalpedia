-- Prove2me | Theorems.Thm_SubmodPerfect_lemma_4_10_forcer_free_star_free_bag
-- name    : SubmodPerfect.lemma_4_10_forcer_free_star_free_bag
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:00.330192+00:00
-- url     : https://prove2.me/theorems/19f63c69-6bf4-4710-bb50-2054eb7bb186
-- title:
--   Lemma 4.10 — the star-free bag contains no copy of a forcer
-- statement:
--   Throughout, the common assumptions of Section 4 hold: $c\in[\tfrac12,1)$, $d\ge\delta\ge1$ are integers, $G$ is a finite graph in which every vertex has degree at most $\delta$, $w:V(G)\to[0,1]$ is a weight function with $w(G)=1$, and $G$ has no $d$-bounded $(w,c)$-balanced separator. Let $S_v=(A_v,C_v,B_v)$ be the canonical star separation of each vertex $v$ and fix an injective ordering $O$ of $V(G)$; $X$ is the $O$-star covering, $\mathcal S=\{S_x:x\in X\}$ the $O$-star covering sequence and $\beta=\bigcap_{S\in\mathcal S}(B(S)\cup C(S))$ the star-free bag. Let $F$ be a forcer for $G$. Then
--
--   $$\text{no }Y\subseteq\beta\text{ has }G[Y]\cong F,$$
--
--   that is, $\beta$ is $F$-free.
--
--   Forcers restrict the star-free bag; with the paw as forcer (Theorem 5.7) this makes $\beta$ paw-free in Section 6.
--
--   Differences from the source:
--   - generalization: G has maximum degree δ → every vertex of G has degree at most δ (δ ≥ 1); reason: the source's statement is the case where δ is the maximum degree; for a graph of maximum degree δ′ ≤ δ the hypotheses on d and the conclusion only weaken with δ, so the source's statement at δ′ implies the Lean one
--   - encoding: the canonical star separations S_v and a fixed ordering O of V(G) → a family S with S v a canonical star separation for v for every v, and an injective O : V → ℕ; reason: under the hypotheses the canonical star separation of every vertex exists and is unique (Lemma 4.1), so quantifying over all choices changes no instance; only the order induced by O is used
--   - encoding: induced subgraphs, paths and weight functions w : V(G) → [0, 1] → vertex sets (Finset), induced paths as lists, and w : V → ℝ with values in [0, 1] on the vertex set; reason: Lean convention; same instances
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Lemma 4.10, p.14 (common assumptions for Section 4, p.10)

import Mathlib
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels
import Definitions.Def_SubmodPerfect_StarSeparations

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Lemma 4.10, p.14.

Let `β` be the star-free bag of `G` and let `F` be a forcer for `G`. Then `β` is `F`-free.

**Formalization Note.** The common assumptions of Section 4 (p.10) are explicit hypotheses: `c ∈ [1/2, 1)`,
positive integers `d ≥ δ`, a weight function `w : V → [0, 1]` with `w(G) = 1`, maximum degree
(at most) `δ`, and no `d`-bounded `(w, c)`-balanced separator. `S v` is a canonical star separation for `v` and `O` is any
injective ordering. "`β` is `F`-free": no subset `Y ⊆ β` induces a graph isomorphic to `F`. -/
theorem lemma_4_10_forcer_free_star_free_bag {V : Type*} [Fintype V]
    (c : ℝ) (hc : 1 / 2 ≤ c ∧ c < 1) (d δ : ℕ) (hδ : 1 ≤ δ) (hdδ : δ ≤ d)
    (G : SimpleGraph V) (w : V → ℝ) (hw : IsWeightFunctionOn w Finset.univ)
    (hw1 : wsum w Finset.univ = 1) (hdeg : MaxDegreeLe G δ)
    (hnosep : ¬ HasBoundedBalancedSepIn G Finset.univ w c d)
    (S : V → Sep V) (hS : ∀ v, IsCanonicalStarSep G w v (S v)) (O : V → ℕ)
    (hO : Function.Injective O) {W : Type*} (F : SimpleGraph W) (hF : IsForcer F G) :
    ∀ Y : Finset V, Y ⊆ starFreeBag S O → ¬ IsCopy G F Y := by sorry

end SubmodPerfect
