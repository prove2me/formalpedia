-- Prove2me | Theorems.Thm_PadbergRao_UpperBound_theorem_3_1
-- name    : PadbergRao.UpperBound.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T23:49:26.248257+00:00
-- url     : https://prove2.me/theorems/56cfeed4-51a7-4701-98b2-f9bd60da0fc7
-- title:
--   Theorem 3.1 — a capacitated blossom inequality is violated iff $G(\bar x,d)$ has an odd cut of capacity $<1$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with incidence matrix $A$, let $b$ be a vector of positive integers on the nodes and $d$ a vector of positive integers on the edges, and let $\bar x$ be a feasible solution of the linear relaxation of the $b$-matching system with upper bounds
--
--   $$
--   Ax\le b,\qquad x\le d,\qquad x\ge 0. \tag{3.1}
--   $$
--
--   Let $G(\bar x,d)$ be the labelled graph built from $\bar x$ and $\bar s=b-A\bar x$ (node set $\tilde V=V\cup\{S\}\cup V_*$, edge weights $\bar y$), for any choice of scan orientation. Then there exist $W\subseteq V$ and $T\subseteq (W:V-W)$ such that $b(W)+d(T)$ is odd and
--
--   $$
--   \bar x(W)+\bar x(T)>\tfrac12\bigl(b(W)+d(T)-1\bigr)
--   $$
--
--   if and only if the cut capacity of an odd minimum cut-set in $G(\bar x,d)$ is less than one, that is, if and only if some $U\subseteq\tilde V$ with an odd number of odd-labelled nodes has $\bar y(U:\tilde V-U)<1$.
--
--   The theorem reduces the separation problem for the blossom inequalities of capacitated $b$-matching to an odd minimum cut-set computation, which Section 1 of the paper solves in polynomial time.
--
--   **Formalization Note** "The cut capacity of an odd minimum cut-set is less than one" is rendered as "some odd cut-set has capacity less than one". The two agree whenever an odd cut-set exists, and when none exists both sides are false (the left side then fails too), so no minimum over a possibly empty family is taken. The sentence "Furthermore, $W$ and $T$ are obtained constructively as in the proof of Lemma 3.2" describes the proof and is not formalized. The graph $G(\bar x,d)$ is built by definitions from $(G,b,d,\bar x)$ and an orientation `tail`, universally quantified; see the definition `graphGxd`.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 77, Theorem 3.1

import Mathlib
import Definitions.Def_PadbergRao_UpperBound_bMatchingSystem
import Definitions.Def_PadbergRao_UpperBound_graphGxd

namespace PadbergRao.UpperBound

/-- Padberg–Rao (1982), p. 77, Theorem 3.1: for a feasible solution `x̄` of (3.1), some blossom
inequality (3.3) is violated by `x̄` (there are `W ⊆ V`, `T ⊆ (W : V − W)` with `b(W) + d(T)` odd
and `x̄(W) + x̄(T) > ½(b(W) + d(T) − 1)`) if and only if an odd minimum cut-set of `G(x̄, d)` has
capacity less than one, i.e. some odd cut-set of `G(x̄, d)` has capacity less than one. -/
theorem theorem_3_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ) (x : Sym2 V → ℝ)
    (hb : ∀ i, 0 < b i) (hd : ∀ e ∈ G.edgeFinset, 0 < d e) (hx : IsFeasible G b d x)
    (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e) :
    (∃ (W : Finset V) (T : Finset (Sym2 V)), IsViolatedBlossom G b d x W T) ↔
      ∃ U : Finset (Node G x), IsOddNodeSet G b d x tail U ∧ yCap G b d x tail U < 1 := by sorry

end PadbergRao.UpperBound
