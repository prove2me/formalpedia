-- Prove2me | Theorems.Thm_ServiceParts_UnitDecomp_lemma2_release_monotone
-- name    : ServiceParts.UnitDecomp.lemma2_release_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T21:52:58.335424+00:00
-- url     : https://prove2.me/theorems/d0529c27-6b9b-4d2c-876b-2c1a58ce90f1
-- title:
--   Lemma 2 — if releasing is uniquely optimal at distance y + 1, releasing is optimal at distance y
-- statement:
--   Consider a single-unit single-customer subsystem over a horizon of $N$ periods ($0<h<b$, $\alpha\in(0,1]$), and let $R^*_n(s,y)\subseteq\{\mathit{Release},\mathit{Hold}\}$ be the set of optimal decisions in period $n$ when the Markov state is $s$, the unit is at the supplier (location $m+1$) and the customer is at distance $y$. For every period $1\le n\le N$, every $s$ and every distance $y\ge 1$,
--   $$R^*_n(s,y+1) = \{\mathit{Release}\} \implies R^*_n(s,y) \ni \mathit{Release}.$$
--
--   Releasing a unit is thus never uniquely optimal for a far customer while strictly suboptimal for a closer one; this is the monotonicity behind the critical distance.
--
--   **Formalization Note** The statement is restricted to $y \ge 1$. At $y = 0$ the customer has already been served, a configuration that never occurs with the unit still at the supplier under a committed policy; there it is false (releasing only adds holding cost), while releasing is uniquely optimal at $y = 1$ whenever the unit can arrive before the horizon ends.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 28, Lemma 2 (R*_n defined on p. 28)

import Mathlib
import Definitions.Def_ServiceParts_UnitDecomp_Model
import Definitions.Def_ServiceParts_UnitDecomp_Subsystem

namespace ServiceParts.UnitDecomp

theorem lemma2_release_monotone {σ : Type} [Fintype σ] (M : Model σ) (N n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (s : σ) (y : ℕ) (hy : 1 ≤ y)
    (hrel : M.optDecisions N n s (y + 1) = {Decision.release}) :
    Decision.release ∈ M.optDecisions N n s y := by sorry

end ServiceParts.UnitDecomp
