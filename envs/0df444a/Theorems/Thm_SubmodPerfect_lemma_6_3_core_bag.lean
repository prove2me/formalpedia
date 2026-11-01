-- Prove2me | Theorems.Thm_SubmodPerfect_lemma_6_3_core_bag
-- name    : SubmodPerfect.lemma_6_3_core_bag
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:58.331359+00:00
-- url     : https://prove2.me/theorems/4871ffa9-a2b8-47e5-9a39-83681abd1be1
-- title:
--   Lemma 6.3 — the core bag lies in the intermediate bag, and components of $G\setminus R$ lie in some $A_x$
-- statement:
--   Throughout, the common assumptions of Sections 6 and 7.1–7.2 hold: $c\in[\tfrac12,1)$, $\delta\ge1$ and $d\ge\delta+3$ are integers, $G$ is a connected paw-friendly graph in which every vertex has degree at most $\delta$, $w:V(G)\to[0,1]$ is a weight function with $w(G)=1$, and $G$ has no $d$-bounded $(w,c)$-balanced separator. $S_v=(A_v,C_v,B_v)$ is the canonical star separation of $v$, $O$ is an injective ordering of $V(G)$, $X$ is the $O$-star covering, and $\beta$ is the star-free bag. Let $(X_1,X_2)$ be a bipartition of $\beta$ into independent sets, $\gamma=\bigcap_{x\in X_2}(B_x\cup C_x)$ the intermediate bag and $R=\beta\cup\bigcup_{x\in X_2}C_x$ the core bag. Then
--
--   1. $R\subseteq\gamma$; and
--   2. every connected component of $G\setminus R$ is contained in $A_x$ for some $x\in\beta$.
--
--   So once $R$ is shown to be an iterated even set, it is an even set separator.
--
--   Differences from the source:
--   - generalization: G has maximum degree δ → every vertex of G has degree at most δ (δ ≥ 1); reason: the source's statement is the case where δ is the maximum degree; for a graph of maximum degree δ′ ≤ δ the hypotheses on d and the conclusion only weaken with δ, so the source's statement at δ′ implies the Lean one
--   - encoding: the canonical star separations S_v and a fixed ordering O of V(G) → a family S with S v a canonical star separation for v for every v, and an injective O : V → ℕ; reason: under the hypotheses the canonical star separation of every vertex exists and is unique (Lemma 4.1), so quantifying over all choices changes no instance; only the order induced by O is used
--   - encoding: induced subgraphs, paths and weight functions w : V(G) → [0, 1] → vertex sets (Finset), induced paths as lists, and w : V → ℝ with values in [0, 1] on the vertex set; reason: Lean convention; same instances
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Lemma 6.3, pp.20–21 (common assumptions for Section 6, pp.19–20)

import Mathlib
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels
import Definitions.Def_SubmodPerfect_StarSeparations

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Lemma 6.3, pp.20–21.

Let `γ` be the intermediate bag and `R` the core bag of `G`. Then (i) `R ⊆ γ`, and (ii) every
connected component of `G \ R` is a subset of `A_x` for some `x ∈ β`.

**Formalization Note.** The common assumptions of Sections 6 and 7.1–7.2 (pp.19–20, p.22) are explicit hypotheses:
`c ∈ [1/2, 1)`, positive integers `d ≥ δ + 3`, `G` connected and paw-friendly with maximum degree
(at most) `δ`, a weight function `w : V → [0, 1]` with `w(G) = 1`, no `d`-bounded
`(w, c)`-balanced separator, a family `S` of canonical star separations (`S v` is a canonical
star separation for `v`), and an ordering `O`. The `O`-star covering is `starCovering S O` and the
star-free bag is `starFreeBag S O`. `(X₁, X₂)` is any bipartition of `β`;
`γ = ⋂_{x ∈ X₂} (B_x ∪ C_x)` and `R = β ∪ ⋃_{x ∈ X₂} C_x` are built from it. -/
theorem lemma_6_3_core_bag {V : Type*} [Fintype V]
    (c : ℝ) (hc : 1 / 2 ≤ c ∧ c < 1) (d δ : ℕ) (hδ : 1 ≤ δ) (hdδ : δ + 3 ≤ d)
    (G : SimpleGraph V) (hconn : G.Connected) (hpf : IsPawFriendly G) (hdeg : MaxDegreeLe G δ)
    (w : V → ℝ) (hw : IsWeightFunctionOn w Finset.univ) (hw1 : wsum w Finset.univ = 1)
    (hnosep : ¬ HasBoundedBalancedSepIn G Finset.univ w c d)
    (S : V → Sep V) (hS : ∀ v, IsCanonicalStarSep G w v (S v)) (O : V → ℕ)
    (hO : Function.Injective O)
    (X₁ X₂ : Finset V) (hbip : IsBipartition G (starFreeBag S O) X₁ X₂) :
    coreBag S (starFreeBag S O) X₂ ⊆ intermediateBag S X₂ ∧
      ∀ D, IsComponentIn G (Finset.univ \ coreBag S (starFreeBag S O) X₂) D →
        ∃ x ∈ starFreeBag S O, D ⊆ (S x).A := by sorry

end SubmodPerfect
