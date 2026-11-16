-- Prove2me | Theorems.Thm_STCSublinear1377_Main_Supplement_lemma_2_2
-- name    : STCSublinear1377.Main.Supplement.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:23:09.115227+00:00
-- url     : https://prove2.me/theorems/caebd8e7-3fd5-432b-98e2-f085ea8c43da
-- title:
--   Lemma 2.2 — Connected one-terminal sub-regions with global boundary at most qk²
-- statement:
--   Let $G$ be a connected simple unweighted graph on $n\ge2$ vertices with $k=\mathrm{STC}(G)$, let $D$ be real, $H=\{v:d_G(v)>D\}$ and $q=|H|$. Let $\{R_v\}_{v\in H}$ be regions: pairwise disjoint vertex sets covering $V(G)$, each inducing a connected subgraph with $R_v\cap H=\{v\}$, such that the number $M$ of edges joining different regions satisfies $M\le(q-1)k$. The **terminals** of $R_v$ are the neighbours of $v$ in $R_v$. Then for every hub $v$ there is a partition of $R_v\setminus\{v\}$ into sets $P$ such that each $G[P]$ is connected, each $P$ contains exactly one terminal, and
--
--   $$b_G(P)\le q\,k^2,$$
--
--   where $b_G(P)$ is the number of edges of $G$ leaving $P$. This bounds the optimum against which Theorem 1.4 is compared in the simple algorithm.
--
--   Differences from the source:
--   - generalization: the regions R₁,…,R_q produced by q − 1 minimum cuts between hubs, with M ≤ (q − 1)k → any partition of V into connected regions, one hub in each, whose inter-region edge count M satisfies M ≤ (q − 1)k; reason: these are the properties of the regions stated on pp.3–4; every region family of the algorithm has them
--   - encoding: the inter-region cut size M → half the sum over regions of b_G(R_v); reason: each inter-region edge is counted once from each side
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Lemma 2.2, PDF/printed p.4; regions defined on pp.3–4

import Definitions.Def_STCSublinear1377_Main_Supplement_Section2
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- Lemma 2.2 for every region family of Section 2: connected regions, one hub each, covering
`V`, with multiway cut `M ≤ (q - 1) k`. Boundaries are global boundaries in `G`. -/
theorem lemma_2_2 :
    ∀ n : ℕ, 2 ≤ n → ∀ g : Table n, isInput g → ∀ D : ℝ,
      ∀ region : Fin n → Finset (Fin n),
      (∀ v ∈ hubs (original g) D, (original g).connectedSet (region v) ∧
        region v ∩ hubs (original g) D = {v}) →
      (∀ u ∈ hubs (original g) D, ∀ v ∈ hubs (original g) D, u ≠ v →
        Disjoint (region u) (region v)) →
      (hubs (original g) D).biUnion region = Finset.univ →
      (∑ v ∈ hubs (original g) D, (original g).boundary (region v)) / 2 ≤
        (((hubs (original g) D).card : ℝ) - 1) * (stc g : ℝ) →
      ∀ v ∈ hubs (original g) D, ∃ parts : Finset (Finset (Fin n)),
        (∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q) ∧
        parts.biUnion id = (region v).erase v ∧
        ∀ P ∈ parts, (original g).connectedSet P ∧
          (regionTerminals g (region v) v ∩ P).card = 1 ∧
          (original g).boundary P ≤ ((hubs (original g) D).card : ℝ) * (stc g : ℝ) ^ 2 := by sorry

end STCSublinear1377.Main.Supplement
