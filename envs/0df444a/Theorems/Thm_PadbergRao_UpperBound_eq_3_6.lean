-- Prove2me | Theorems.Thm_PadbergRao_UpperBound_eq_3_6
-- name    : PadbergRao.UpperBound.eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T23:25:54.321998+00:00
-- url     : https://prove2.me/theorems/880ae605-fc5d-4e2c-8c76-49d016a4bd38
-- title:
--   Eq. (3.6) — $2x(W)+x(W:V-W)+x(T)+s(W)+t(T)=b(W)+d(T)$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with node capacities $b$ and edge bounds $d$, let $x\in\mathbb{R}^E$ be any point, and let $s=b-Ax$ and $t=d-x$ be the slack vectors of the constraints $Ax\le b$ and $x\le d$. For every $W\subseteq V$ and every $T\subseteq (W:V-W)$,
--
--   $$
--   2x(W)+x(W:V-W)+x(T)+s(W)+t(T)=b(W)+d(T),
--   $$
--
--   where $x(W)=\sum_{e\in E(W)}x_e$, $x(W:V-W)=\sum_{e\in(W:V-W)}x_e$, $x(T)=\sum_{e\in T}x_e$, $s(W)=\sum_{i\in W}s_i$ and $t(T)=\sum_{e\in T}(d_e-x_e)$.
--
--   The identity is obtained by adding the rows of $Ax+s=b$ indexed by $W$ and the rows of $x+t=d$ indexed by $T$. It is what turns the blossom inequality (3.3) into a cut condition.
--
--   **Formalization Note** The identity is stated for an arbitrary real vector $x$; neither feasibility nor positivity of $b,d$ is needed.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 75, Section 3, Eq. (3.6) (with (3.4))

import Mathlib
import Definitions.Def_PadbergRao_UpperBound_bMatchingSystem

namespace PadbergRao.UpperBound

/-- Padberg–Rao (1982), p. 75, Eq. (3.6): adding the rows of `Ax + s = b` with index in `W`
and the rows of `x + t = d` with index in `T ⊆ (W : V − W)` gives
`2x(W) + x(W : V − W) + x(T) + s(W) + t(T) = b(W) + d(T)`. -/
theorem eq_3_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V → ℕ) (d : Sym2 V → ℕ) (x : Sym2 V → ℝ) (W : Finset V) (T : Finset (Sym2 V))
    (hT : T ⊆ cutEdges G W) :
    2 * (∑ e ∈ edgesWithin G W, x e) + (∑ e ∈ cutEdges G W, x e) + (∑ e ∈ T, x e)
        + (∑ i ∈ W, slack G b x i) + (∑ e ∈ T, ((d e : ℝ) - x e))
      = (∑ i ∈ W, (b i : ℝ)) + ∑ e ∈ T, (d e : ℝ) := by sorry

end PadbergRao.UpperBound
