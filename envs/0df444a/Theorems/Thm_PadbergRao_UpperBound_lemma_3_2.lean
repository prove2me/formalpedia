-- Prove2me | Theorems.Thm_PadbergRao_UpperBound_lemma_3_2
-- name    : PadbergRao.UpperBound.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T23:41:47.789531+00:00
-- url     : https://prove2.me/theorems/262ef534-0b55-4ad6-b791-2298e3eb284d
-- title:
--   Lemma 3.2 — an odd cut-set of $G(\bar x,d)$ of capacity $<1$ avoiding $S$ yields $(W,T)$ satisfying (3.8)
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, $b$ a vector of positive integers on the nodes, $d$ a vector of positive integers on the edges, and $\bar x$ a feasible solution of the linear relaxation of (3.1), with node slacks $\bar s=b-A\bar x$. Let $G(\bar x,d)$ be the labelled graph with node set $\tilde V=V\cup\{S\}\cup V_*$ and edge weights $\bar y$, built with any choice of scan orientation.
--
--   Let $(U:\tilde V-U)$ be an odd cut-set in $G(\bar x,d)$ with cut capacity $c=\bar y(U:\tilde V-U)<1$ and such that $S\notin U$. Then there exist $W\subseteq V$ and $T\subseteq (W:V-W)$ such that $b(W)+d(T)$ is odd and
--
--   $$
--   \bar x(W:V-W)+d(T)-2\bar x(T)+\bar s(W)=\bar y(U:\tilde V-U). \tag{3.8}
--   $$
--
--   This is the converse direction of the reduction: every odd cut-set of $G(\bar x,d)$ of capacity less than one yields a violated blossom inequality.
--
--   **Formalization Note** Feasibility of $\bar x$ and positivity of $b$ and $d$ are the standing assumptions of Section 3 and are stated as hypotheses. The orientation `tail` is universally quantified. The paper's constructive description of $W$ and $T$ (from the proof) is not part of the statement.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 76, Lemma 3.2 (proof continues on p. 77)

import Mathlib
import Definitions.Def_PadbergRao_UpperBound_bMatchingSystem
import Definitions.Def_PadbergRao_UpperBound_graphGxd

namespace PadbergRao.UpperBound

/-- Padberg–Rao (1982), p. 76, Lemma 3.2: if `(U : Ṽ − U)` is an odd cut-set of `G(x̄, d)` with
cut capacity `ȳ(U : Ṽ − U) < 1` and `S ∉ U`, then there are `W ⊆ V` and `T ⊆ (W : V − W)` with
`b(W) + d(T)` odd and `x̄(W : V − W) + d(T) − 2x̄(T) + s̄(W) = ȳ(U : Ṽ − U)` (Eq. (3.8)). -/
theorem lemma_3_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ) (x : Sym2 V → ℝ)
    (hb : ∀ i, 0 < b i) (hd : ∀ e ∈ G.edgeFinset, 0 < d e) (hx : IsFeasible G b d x)
    (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e)
    (U : Finset (Node G x)) (hU : IsOddNodeSet G b d x tail U)
    (hcap : yCap G b d x tail U < 1) (hS : specialNode G x ∉ U) :
    ∃ (W : Finset V) (T : Finset (Sym2 V)), T ⊆ cutEdges G W ∧
      Odd (∑ i ∈ W, b i + ∑ e ∈ T, d e) ∧
      (∑ e ∈ cutEdges G W, x e) + (∑ e ∈ T, (d e : ℝ)) - 2 * (∑ e ∈ T, x e)
          + (∑ i ∈ W, slack G b x i)
        = yCap G b d x tail U := by sorry

end PadbergRao.UpperBound
