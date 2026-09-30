-- Prove2me | Theorems.Thm_PadbergRao_UpperBound_eq_3_7
-- name    : PadbergRao.UpperBound.eq_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T23:31:41.838391+00:00
-- url     : https://prove2.me/theorems/a06c7c1a-f058-4173-bab5-9cdf28d0589d
-- title:
--   Eq. (3.7) — a blossom inequality is violated iff $\bar x(W:V-W)+d(T)-2\bar x(T)+\bar s(W)<1$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with node capacities $b$ and edge bounds $d$, let $\bar x\in\mathbb{R}^E$ and let $\bar s=b-A\bar x$ be its node slacks. For every $W\subseteq V$ and every $T\subseteq (W:V-W)$,
--
--   $$
--   \bar x(W)+\bar x(T)>\tfrac12\bigl(b(W)+d(T)-1\bigr)
--   \iff
--   \bar x(W:V-W)+d(T)-2\bar x(T)+\bar s(W)<1,
--   $$
--
--   where $\bar x(W)=\sum_{e\in E(W)}\bar x_e$ and $\bar x(W:V-W)$ is the sum of $\bar x_e$ over the cut-set of $W$.
--
--   The right-hand side is a cut-set condition: edges of $(W:V-W)-T$ appear with value $\bar x_e$, edges of $T$ in complemented form $d_e-\bar x_e$, and each node of $W$ contributes its slack. This rewriting of the violated blossom inequality is what the proof of Theorem 3.1 uses.
--
--   **Formalization Note** The equivalence is stated for an arbitrary real vector $\bar x$; the oddness of $b(W)+d(T)$ plays no role in it.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 75, Section 3, Eq. (3.7) (equivalence with (3.3) used on p. 77 in the proof of Theorem 3.1)

import Mathlib
import Definitions.Def_PadbergRao_UpperBound_bMatchingSystem

namespace PadbergRao.UpperBound

/-- Padberg–Rao (1982), p. 75, Eq. (3.7): for `T ⊆ (W : V − W)`, the point `x̄` violates the
blossom inequality (3.3), `x̄(W) + x̄(T) > ½(b(W) + d(T) − 1)`, if and only if
`x̄(W : V − W) + d(T) − 2x̄(T) + s̄(W) < 1`. -/
theorem eq_3_7 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V → ℕ) (d : Sym2 V → ℕ) (x : Sym2 V → ℝ) (W : Finset V) (T : Finset (Sym2 V))
    (hT : T ⊆ cutEdges G W) :
    ((∑ i ∈ W, (b i : ℝ)) + (∑ e ∈ T, (d e : ℝ)) - 1) / 2
        < (∑ e ∈ edgesWithin G W, x e) + ∑ e ∈ T, x e ↔
      (∑ e ∈ cutEdges G W, x e) + (∑ e ∈ T, (d e : ℝ)) - 2 * (∑ e ∈ T, x e)
        + (∑ i ∈ W, slack G b x i) < 1 := by sorry

end PadbergRao.UpperBound
