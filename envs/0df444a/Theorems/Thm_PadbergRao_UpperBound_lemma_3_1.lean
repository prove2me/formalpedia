-- Prove2me | Theorems.Thm_PadbergRao_UpperBound_lemma_3_1
-- name    : PadbergRao.UpperBound.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T23:36:20.469259+00:00
-- url     : https://prove2.me/theorems/0788fed3-c8df-4fa6-b2cc-f12fe8983f34
-- title:
--   Lemma 3.1 — an odd pair $(W,T)$ with $T\subseteq E(\bar x)$ yields an odd cut-set of $G(\bar x,d)$ of equal capacity
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, $b$ a vector of positive integers on the nodes, $d$ a vector of positive integers on the edges, and $\bar x$ a feasible solution of the linear relaxation of (3.1), with node slacks $\bar s=b-A\bar x$. Let $G(\bar x,d)$ be the labelled graph with node set $\tilde V=V\cup\{S\}\cup V_*$ and edge weights $\bar y$, built with any choice of scan orientation.
--
--   Let $W\subseteq V$ and $T\subseteq (W:V-W)\cap E(\bar x)$ be such that $b(W)+d(T)$ is odd. Then there exists an odd cut-set $(U:\tilde V-U)$ in $G(\bar x,d)$ with $S\in\tilde V-U$ such that
--
--   $$
--   \bar x(W:V-W)+d(T)-2\bar x(T)+\bar s(W)=\bar y(U:\tilde V-U). \tag{3.8}
--   $$
--
--   Together with (3.7) this shows that every violated blossom inequality produces an odd cut-set of $G(\bar x,d)$ of capacity less than one.
--
--   **Formalization Note** $E(\bar x)$ is the set of edges with $\bar x_e>0$. Feasibility of $\bar x$ and positivity of $b$ and $d$ are the standing assumptions of Section 3 and are stated as hypotheses. The orientation `tail` (the end of each edge scanned first) is universally quantified.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 76, Lemma 3.1, Eq. (3.8)

import Mathlib
import Definitions.Def_PadbergRao_UpperBound_bMatchingSystem
import Definitions.Def_PadbergRao_UpperBound_graphGxd

namespace PadbergRao.UpperBound

/-- Padberg–Rao (1982), p. 76, Lemma 3.1: if `W ⊆ V`, `T ⊆ (W : V − W) ∩ E(x̄)` and
`b(W) + d(T)` is odd, then some odd cut-set `(U : Ṽ − U)` of `G(x̄, d)` with `S ∉ U` has
`x̄(W : V − W) + d(T) − 2x̄(T) + s̄(W) = ȳ(U : Ṽ − U)` (Eq. (3.8)). -/
theorem lemma_3_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ) (x : Sym2 V → ℝ)
    (hb : ∀ i, 0 < b i) (hd : ∀ e ∈ G.edgeFinset, 0 < d e) (hx : IsFeasible G b d x)
    (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e)
    (W : Finset V) (T : Finset (Sym2 V)) (hT : T ⊆ cutEdges G W ∩ posEdges G x)
    (hodd : Odd (∑ i ∈ W, b i + ∑ e ∈ T, d e)) :
    ∃ U : Finset (Node G x), IsOddNodeSet G b d x tail U ∧ specialNode G x ∉ U ∧
      (∑ e ∈ cutEdges G W, x e) + (∑ e ∈ T, (d e : ℝ)) - 2 * (∑ e ∈ T, x e)
          + (∑ i ∈ W, slack G b x i)
        = yCap G b d x tail U := by sorry

end PadbergRao.UpperBound
