-- Prove2me | Theorems.Thm_SubmodPerfect_lemma_4_8_star_free_bag_properties
-- name    : SubmodPerfect.lemma_4_8_star_free_bag_properties
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:07.260693+00:00
-- url     : https://prove2.me/theorems/a355e239-90a0-4ad5-aea0-c53ed0757e32
-- title:
--   Lemma 4.8 — the star-free bag contains $X$, is connected and has no $(d-k)$-bounded balanced separator
-- statement:
--   Throughout, the common assumptions of Section 4 hold: $c\in[\tfrac12,1)$, $d\ge\delta\ge1$ are integers, $G$ is a finite graph in which every vertex has degree at most $\delta$, $w:V(G)\to[0,1]$ is a weight function with $w(G)=1$, and $G$ has no $d$-bounded $(w,c)$-balanced separator. Let $S_v=(A_v,C_v,B_v)$ be the canonical star separation of each vertex $v$ and fix an injective ordering $O$ of $V(G)$; $X$ is the $O$-star covering, $\mathcal S=\{S_x:x\in X\}$ the $O$-star covering sequence and $\beta=\bigcap_{S\in\mathcal S}(B(S)\cup C(S))$ the star-free bag. Suppose $\dim(\mathcal S)=k$, $G$ is connected and $d\ge k$. Then
--
--   1. $X\subseteq\beta$;
--   2. $G[\beta]$ is connected;
--   3. there is a weight function $w_\beta:\beta\to[0,1]$ with $w_\beta(\beta)=1$ and $\max_{v\in\beta}w_\beta(v)\le\max_vw(v)+(1-c)$; and
--   4. for this $w_\beta$, $G[\beta]$ has no $(d-k)$-bounded $(w_\beta,c)$-balanced separator.
--
--   The star-free bag inherits the absence of bounded balanced separators, with the loss controlled by the dimension $k\le\delta+1$; this is what makes $\beta$ well structured in Section 6.
--
--   **Formalization Note** The maximum-weight bound is written vertexwise: each $w_\beta(v)$, $v\in\beta$, is at most $w(u)+(1-c)$ for some vertex $u$.
--
--   Differences from the source:
--   - generalization: G has maximum degree δ → every vertex of G has degree at most δ (δ ≥ 1); reason: the source's statement is the case where δ is the maximum degree; for a graph of maximum degree δ′ ≤ δ the hypotheses on d and the conclusion only weaken with δ, so the source's statement at δ′ implies the Lean one
--   - encoding: the canonical star separations S_v and a fixed ordering O of V(G) → a family S with S v a canonical star separation for v for every v, and an injective O : V → ℕ; reason: under the hypotheses the canonical star separation of every vertex exists and is unique (Lemma 4.1), so quantifying over all choices changes no instance; only the order induced by O is used
--   - encoding: w_β^max ≤ w^max + (1 − c) → every w_β(v), v ∈ β, is at most w(u) + (1 − c) for some vertex u; reason: a finite maximum is attained; equivalent
--   - encoding: induced subgraphs, paths and weight functions w : V(G) → [0, 1] → vertex sets (Finset), induced paths as lists, and w : V → ℝ with values in [0, 1] on the vertex set; reason: Lean convention; same instances
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Lemma 4.8, p.13 (common assumptions for Section 4, p.10)

import Mathlib
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels
import Definitions.Def_SubmodPerfect_StarSeparations

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Lemma 4.8, p.13.

Let `X` be the `O`-star covering of `G`, `𝒮` the `O`-star covering sequence, `dim(𝒮) = k`, `β`
the star-free bag; suppose `G` is connected and `d ≥ k`. Then (i) `X ⊆ β`, (ii) `β` is connected,
(iii) there is a weight function `w_β : β → [0, 1]` with `w_β(β) = 1` and
`w_β^max ≤ w^max + (1 − c)`, and (iv) `β` has no `(d − k)`-bounded `(w_β, c)`-balanced separator.

**Formalization Note.** The common assumptions of Section 4 (p.10) are explicit hypotheses: `c ∈ [1/2, 1)`,
positive integers `d ≥ δ`, a weight function `w : V → [0, 1]` with `w(G) = 1`, maximum degree
(at most) `δ`, and no `d`-bounded `(w, c)`-balanced separator. `S v` is a canonical star separation for `v` (any choice; it
is unique under these hypotheses by Lemma 4.1) and `O` is any injective ordering. The bound
`w_β^max ≤ w^max + (1 − c)` is written vertexwise: every `w_β(v)`, `v ∈ β`, is at most
`w(u) + (1 − c)` for some vertex `u`. Items (iii) and (iv) refer to the same `w_β`. Balls and
components in (iv) are those of `G[β]`. -/
theorem lemma_4_8_star_free_bag_properties {V : Type*} [Fintype V]
    (c : ℝ) (hc : 1 / 2 ≤ c ∧ c < 1) (d δ : ℕ) (hδ : 1 ≤ δ) (hdδ : δ ≤ d)
    (G : SimpleGraph V) (w : V → ℝ) (hw : IsWeightFunctionOn w Finset.univ)
    (hw1 : wsum w Finset.univ = 1) (hdeg : MaxDegreeLe G δ)
    (hnosep : ¬ HasBoundedBalancedSepIn G Finset.univ w c d)
    (S : V → Sep V) (hS : ∀ v, IsCanonicalStarSep G w v (S v)) (O : V → ℕ)
    (hO : Function.Injective O) (k : ℕ) (hk : IsDim S (starCovering S O) k)
    (hconn : G.Connected) (hdk : k ≤ d) :
    starCovering S O ⊆ starFreeBag S O ∧
      (G.induce ((starFreeBag S O : Finset V) : Set V)).Connected ∧
      ∃ wβ : V → ℝ, IsWeightFunctionOn wβ (starFreeBag S O) ∧
        wsum wβ (starFreeBag S O) = 1 ∧
        (∀ v ∈ starFreeBag S O, ∃ u, wβ v ≤ w u + (1 - c)) ∧
        ¬ HasBoundedBalancedSepIn G (starFreeBag S O) wβ c (d - k) := by sorry

end SubmodPerfect
