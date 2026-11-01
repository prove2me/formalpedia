-- Prove2me | Theorems.Thm_SubmodPerfect_lemma_7_5_bipartition_even_sets
-- name    : SubmodPerfect.lemma_7_5_bipartition_even_sets
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:11.76505+00:00
-- url     : https://prove2.me/theorems/1a2ee180-6a6e-4ef6-b8ac-489a86a4aded
-- title:
--   Lemma 7.5 — the two sides of the star-free bag are even sets of $G$
-- statement:
--   Throughout, the common assumptions of Sections 6 and 7.1–7.2 hold: $c\in[\tfrac12,1)$, $\delta\ge1$ and $d\ge\delta+3$ are integers, $G$ is a connected paw-friendly graph in which every vertex has degree at most $\delta$, $w:V(G)\to[0,1]$ is a weight function with $w(G)=1$, and $G$ has no $d$-bounded $(w,c)$-balanced separator. $S_v=(A_v,C_v,B_v)$ is the canonical star separation of $v$, $O$ is an injective ordering of $V(G)$, $X$ is the $O$-star covering, and $\beta$ is the star-free bag. Let $(X_1,X_2)$ be a bipartition of $\beta$ into independent sets. Then
--
--   $$X_1\text{ and }X_2\text{ are even sets of }G.$$
--
--   These are the first two entries of the even set separator of Lemma 8.1.
--
--   Differences from the source:
--   - generalization: G has maximum degree δ → every vertex of G has degree at most δ (δ ≥ 1); reason: the source's statement is the case where δ is the maximum degree; for a graph of maximum degree δ′ ≤ δ the hypotheses on d and the conclusion only weaken with δ, so the source's statement at δ′ implies the Lean one
--   - encoding: the canonical star separations S_v and a fixed ordering O of V(G) → a family S with S v a canonical star separation for v for every v, and an injective O : V → ℕ; reason: under the hypotheses the canonical star separation of every vertex exists and is unique (Lemma 4.1), so quantifying over all choices changes no instance; only the order induced by O is used
--   - encoding: induced subgraphs, paths and weight functions w : V(G) → [0, 1] → vertex sets (Finset), induced paths as lists, and w : V → ℝ with values in [0, 1] on the vertex set; reason: Lean convention; same instances
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Lemma 7.5, p.23 (common assumptions for Sections 7.1 and 7.2, p.22)

import Mathlib
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels
import Definitions.Def_SubmodPerfect_StarSeparations

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Lemma 7.5, p.23.

Let `(X₁, X₂)` be the bipartition of `β`. Then `X₁` and `X₂` are even sets in `G`.

**Formalization Note.** The common assumptions of Sections 6 and 7.1–7.2 (pp.19–20, p.22) are explicit hypotheses:
`c ∈ [1/2, 1)`, positive integers `d ≥ δ + 3`, `G` connected and paw-friendly with maximum degree
(at most) `δ`, a weight function `w : V → [0, 1]` with `w(G) = 1`, no `d`-bounded
`(w, c)`-balanced separator, a family `S` of canonical star separations (`S v` is a canonical
star separation for `v`), and an ordering `O`. The `O`-star covering is `starCovering S O` and the
star-free bag is `starFreeBag S O`. `(X₁, X₂)` is any bipartition of `β`. -/
theorem lemma_7_5_bipartition_even_sets {V : Type*} [Fintype V]
    (c : ℝ) (hc : 1 / 2 ≤ c ∧ c < 1) (d δ : ℕ) (hδ : 1 ≤ δ) (hdδ : δ + 3 ≤ d)
    (G : SimpleGraph V) (hconn : G.Connected) (hpf : IsPawFriendly G) (hdeg : MaxDegreeLe G δ)
    (w : V → ℝ) (hw : IsWeightFunctionOn w Finset.univ) (hw1 : wsum w Finset.univ = 1)
    (hnosep : ¬ HasBoundedBalancedSepIn G Finset.univ w c d)
    (S : V → Sep V) (hS : ∀ v, IsCanonicalStarSep G w v (S v)) (O : V → ℕ)
    (hO : Function.Injective O)
    (X₁ X₂ : Finset V) (hbip : IsBipartition G (starFreeBag S O) X₁ X₂) :
    IsEvenSetIn G Finset.univ X₁ ∧ IsEvenSetIn G Finset.univ X₂ := by sorry

end SubmodPerfect
