-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_2_9
-- name    : SemiStreamMWM.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:30:57.248469+00:00
-- url     : https://prove2.me/theorems/681d260b-eb28-4898-801e-0e6136466360
-- title:
--   Lemma 2.9 — internal and positive crossing matchings implement the step oracle
-- statement:
--   Let $G$ have integer weights in $[1,W]$, $W\ge8$ a power of two; fix $0<t\le1/(32\log W)$, $\delta=t\log W$ and $\eta$ as in §2.1. Let $x\in\mathcal P_{G,\delta}$ and let $\mathcal Q$ be a partition of $V$ whose odd-set guarantee (property 2 of Lemma 3.1) holds for $x$, with internal graph $H$. Under the edge weights $r=-\nabla F_t(x)$, let $I$ be a $(1-\delta)$-MWM in $H$ and $J$ an $(\alpha,O(\delta\mu_w(G)))$-MWM in $G\setminus H$ for an absolute constant $\alpha\in(0,1]$, with every edge of $J$ of positive weight. Then for a sufficiently large absolute constant $c$, one of the directions
--
--   $$d=(1-2\delta)\vec1_I-x\qquad\text{or}\qquad d=\vec1_J$$
--
--   is an admissible answer of $\mathtt{Step}(x,t)$ in the sense of Definition 2.4.
--
--   Together with Lemmas 3.3 and 3.4 this implements the step oracle by two matching computations.
--
--   Differences from the source:
--   - encoding: O(δµ_w(G)) and a sufficiently large absolute constant c → B·δ·µ_w(G) with B ≥ 0 fixed after α; ∃ c₀ ≥ 1 after α and B with the conclusion for every c ≥ c₀, before the graph; reason: absolute constants come before the instance
--   - encoding: a partition Q of V → a `Finpartition` of the vertex set, its internal edges, and the odd-set guarantee `OddSetGuarantee`; reason: the same object
--   - encoding: the standing assumptions stated once for the paper and for §2.1 (integer weights in [1, W], W ≥ 8 a power of two, 0 < t ≤ 1/(32 log W)) → hypotheses `Standing G w W`, `0 < t`, `t ≤ 1/(32 * logW W)`; reason: trap 19: the section's assumptions are binders; no instance changes
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 2.9, p.13

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_Potential
import Definitions.Def_SemiStreamMWM_Algorithms
import Definitions.Def_SemiStreamMWM_CutPartition

open Classical

namespace SemiStreamMWM

/-- J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 2.9, p.13.

"Let x ∈ P_{G,δ}, and let Q be a partition whose odd-set guarantee in Lemma 3.1 holds for x, with
internal graph H. Under edge weights −∇F_t(x), let I be a (1 − δ)-MWM in H and J an
(α, O(δµ_w(G)))-MWM in G \ H for an absolute constant α ∈ (0, 1], containing only positive-weight
edges. A direction d ∈ {(1 − 2δ)1_I − x, 1_J} satisfies Definition 2.4 for a sufficiently large absolute
constant c."

**Formalization Note.** `Q` is a partition of the vertex set (`Finpartition`), `H` its internal
edges; the odd-set guarantee of Lemma 3.1 (property 2, p.14) is `OddSetGuarantee`. `O(δµ_w(G))` is
`B·δ·µ_w(G)` with `B ≥ 0` fixed before `c`, and "sufficiently large `c`" is a threshold `c₀ ≥ 1`
before the graph. Satisfying Definition 2.4 (both items) is `StepOK`, with the step size `η` and
`δ = t log W` of §2.1 and its standing `0 < t ≤ 1/(32 log W)`. -/
theorem lemma_2_9 : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ B : ℝ, 0 ≤ B → ∃ c₀ : ℝ, 1 ≤ c₀ ∧
    ∀ c : ℝ, c₀ ≤ c →
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (t : ℝ)
      (x : G.edgeSet → ℝ) (Q : Finpartition (Finset.univ : Finset V)) (I J : Finset G.edgeSet),
      Standing G w W → 0 < t → t ≤ 1 / (32 * logW W) → x ∈ truncPolytope G (delta W t) →
      OddSetGuarantee G (Q.parts : Set (Finset V)) (delta W t) x →
      IsApproxMWM G (-gradF G w W t x) (internalEdges G (Q.parts : Set (Finset V)))
        (1 - delta W t) 0 I →
      IsApproxMWM G (-gradF G w W t x) (internalEdges G (Q.parts : Set (Finset V)))ᶜ α
        (B * delta W t * mwm G w) J →
      (∀ e ∈ J, 0 < -gradF G w W t x e) →
      StepOK G w W c t x ((1 - 2 * delta W t) • ind G I - x) ∨ StepOK G w W c t x (ind G J) := by sorry

end SemiStreamMWM
