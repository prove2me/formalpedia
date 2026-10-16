-- Prove2me | Theorems.Thm_StrategicAlloc_RRExists_theorem_A_3
-- name    : StrategicAlloc.RRExists.theorem_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:35:58.622577+00:00
-- url     : https://prove2.me/theorems/4e2b10d1-95b0-4708-9e46-cf8560cd3dc6
-- title:
--   Theorem A.3 — Round-Robin has a pure Nash equilibrium in every instance with additive valuations
-- statement:
--   Let $\mathcal I = (N, M, v)$ be any instance with $n \ge 1$ agents, $m$ goods and additive valuations with non-negative values $v_i(g) \ge 0$; values may be zero and may tie. Then Round-Robin (Mechanism 1, lexicographic tie-breaking of bids) has at least one pure Nash equilibrium:
--   $$\exists\, \mathbf b \in (\mathbb R^m_{\ge 0})^n \ \ \forall i \in N\ \ \forall \mathbf b'_i \in \mathbb R^m_{\ge 0}:\quad v_i\big(\text{RR}(\mathbf b'_i, \mathbf b_{-i})_i\big) \le v_i\big(\text{RR}(\mathbf b)_i\big).$$
--
--   This extends the existence result of Aziz, Goldberg and Walsh (Theorem A.2), which needs positive values and strict preferences, to general additive valuations. Combined with Theorem 3.3 of the same paper (every PNE of Round-Robin is EF1 with respect to the true valuations), it shows that Round-Robin always has equilibria and that all of them are fair in the EF1 sense.
--
--   **Formalization Note** Agents are `Fin n` with `[NeZero n]`, goods `Fin m`. The equilibrium is over bid vectors in $\mathbb R^m_{\ge 0}$ with deviations over all such vectors, and the bundle values are the true $v_i$. No positivity or strictness is assumed: those are exactly what the theorem removes from Theorem A.2.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 24, Theorem A.3

import Mathlib
import Definitions.Def_StrategicAlloc_RRExists_Setting

namespace StrategicAlloc.RRExists

/-- Theorem A.3 (p. 24): for every instance with additive non-negative valuations, Round-Robin
(Mechanism 1, lexicographic tie-breaking) has at least one pure Nash equilibrium. -/
theorem theorem_A_3 {n m : ℕ} [NeZero n] (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ b : Fin n → Fin m → ℝ, StrategicAlloc.RRFair.IsPNE StrategicAlloc.RRFair.roundRobin v b := by sorry

end StrategicAlloc.RRExists
