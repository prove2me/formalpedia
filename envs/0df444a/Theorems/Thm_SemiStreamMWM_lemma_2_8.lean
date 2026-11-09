-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_2_8
-- name    : SemiStreamMWM.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:25:55.04323+00:00
-- url     : https://prove2.me/theorems/64f10af0-e1b0-433c-b78c-e4b361b6c3d4
-- title:
--   Lemma 2.8 — the better of the internal and crossing directions is an approximate best direction
-- statement:
--   Let $G$ have integer weights in $[1,W]$, $W\ge8$ a power of two; fix $0<t\le1/(32\log W)$ and $\delta=t\log W$. Let $x\in\mathcal P_{G,\delta}$ and $H\subseteq E$. Under the edge weights $r=-\nabla F_t(x)$, let $I$ be a $(1-\delta)$-MWM in $H$ and $J$ an $(\alpha,O(\delta\mu_w(G)))$-MWM in $G\setminus H$, for an absolute constant $\alpha\in(0,1]$. Then for every sufficiently large absolute constant $c\ge1$ there is $d\in\{(1-2\delta)\vec1_I-x,\ \vec1_J\}$ with
--
--   $$\nabla F_t(x)^\top d\le\frac1c\min_{d':\,x+d'\in\mathcal P_G}\nabla F_t(x)^\top d'+c\,\delta\mu_w(G).$$
--
--   This reduces the step oracle to two approximate matching problems.
--
--   Differences from the source:
--   - encoding: O(δµ_w(G)) and a sufficiently large absolute constant c → B·δ·µ_w(G) with B ≥ 0 fixed after α; ∃ c₀ ≥ 1 after α and B with the conclusion for every c ≥ c₀, before the graph; reason: absolute constants come before the instance
--   - encoding: min over {d′ : x + d′ ∈ P_G} → the bound against every d′ with x + d′ ∈ P_G; reason: the minimum is attained on the compact set, so the two are equivalent
--   - encoding: the standing assumptions stated once for the paper and for §2.1 (integer weights in [1, W], W ≥ 8 a power of two, 0 < t ≤ 1/(32 log W)) → hypotheses `Standing G w W`, `0 < t`, `t ≤ 1/(32 * logW W)`; reason: trap 19: the section's assumptions are binders; no instance changes
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 2.8, p.13

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_Potential

open Classical

namespace SemiStreamMWM

/-- J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 2.8, p.13.

"Let x ∈ P_{G,δ}, H ⊆ G. Under edge weights −∇F_t(x), let I be a (1 − δ)-MWM in H, and J be an
(α, O(δµ_w(G)))-MWM in G \ H, for an absolute constant α ∈ (0, 1]. For a sufficiently large absolute
constant c ≥ 1, there exists d ∈ {(1 − 2δ)1_I − x, 1_J} such that
∇F_t(x)^⊤d ≤ (1/c) min_{d′ : x+d′∈P_G} ∇F_t(x)^⊤d′ + cδµ_w(G)."

**Formalization Note.** `H ⊆ G` is a set of edges and `G \ H` its complement. The `O(δµ_w(G))` is
`B·δ·µ_w(G)` with the absolute constant `B ≥ 0` fixed, like `α`, before `c`; "sufficiently large `c`"
is a threshold `c₀ ≥ 1` with the conclusion for every `c ≥ c₀`, before the graph and the point. §2.1's
`0 < t ≤ 1/(32 log W)`, `δ = t log W` and footnote 1 (`Standing`) are hypotheses. The minimum over
`{d′ : x + d′ ∈ P_G}` is attained, so the bound against the minimum is the bound against every such
`d′`. -/
theorem lemma_2_8 : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ B : ℝ, 0 ≤ B → ∃ c₀ : ℝ, 1 ≤ c₀ ∧
    ∀ c : ℝ, c₀ ≤ c →
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (t : ℝ)
      (x : G.edgeSet → ℝ) (H I J : Finset G.edgeSet),
      Standing G w W → 0 < t → t ≤ 1 / (32 * logW W) → x ∈ truncPolytope G (delta W t) →
      IsApproxMWM G (-gradF G w W t x) H (1 - delta W t) 0 I →
      IsApproxMWM G (-gradF G w W t x) Hᶜ α (B * delta W t * mwm G w) J →
      ∃ d ∈ ({(1 - 2 * delta W t) • ind G I - x, ind G J} : Set (G.edgeSet → ℝ)),
        ∀ d' : G.edgeSet → ℝ, x + d' ∈ matchingPolytope G →
          wdot G (gradF G w W t x) d ≤
            (1 / c) * wdot G (gradF G w W t x) d' + c * delta W t * mwm G w := by sorry

end SemiStreamMWM
