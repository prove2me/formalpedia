-- Prove2me | Theorems.Thm_StrategicAlloc_RRExists_theorem_A_2
-- name    : StrategicAlloc.RRExists.theorem_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:36:03.935354+00:00
-- url     : https://prove2.me/theorems/66ccd729-5a25-4745-9fea-5286fd56f074
-- title:
--   Theorem A.2 — Round-Robin has a PNE when all values are positive and strict
-- statement:
--   Consider an instance with $n \ge 1$ agents and $m$ goods in which every agent values every good positively, $v_i(g) > 0$, and every agent's values are pairwise distinct, $v_i(g) \ne v_i(h)$ for $g \ne h$ (so $v_i$ induces a strict preference ranking over the goods). Then Round-Robin (Mechanism 1, with lexicographic tie-breaking of bids) has a pure Nash equilibrium:
--   $$\exists\, \mathbf b \in (\mathbb R^m_{\ge 0})^n \ \text{such that for all } i \text{ and all } \mathbf b'_i \in \mathbb R^m_{\ge 0}:\quad v_i\big(\text{RR}(\mathbf b'_i, \mathbf b_{-i})_i\big) \le v_i\big(\text{RR}(\mathbf b)_i\big).$$
--
--   The paper attributes this to Aziz, Goldberg and Walsh (bluff profiles) and does not prove it. It is the special case from which Theorem A.3 is derived by perturbing the valuations.
--
--   **Formalization Note** The equilibrium is over bid vectors with deviations ranging over every non-negative bid vector, and the mechanism breaks ties in bids lexicographically; this is the paper's notion, not the ranking-based equilibrium of the cited work. Strictness is `Function.Injective (v i)`.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 24, Theorem A.2 (follows from Aziz, Goldberg, Walsh, ADT 2017)

import Mathlib
import Definitions.Def_StrategicAlloc_RRExists_Setting

namespace StrategicAlloc.RRExists

/-- Theorem A.2 (p. 24, follows from Aziz–Goldberg–Walsh): if all values are positive and every
agent's values are pairwise distinct, Round-Robin has at least one pure Nash equilibrium. -/
theorem theorem_A_2 {n m : ℕ} [NeZero n] (v : Fin n → Fin m → ℝ) (hpos : ∀ i g, 0 < v i g)
    (hstrict : ∀ i, Function.Injective (v i)) :
    ∃ b : Fin n → Fin m → ℝ, StrategicAlloc.RRFair.IsPNE StrategicAlloc.RRFair.roundRobin v b := by sorry

end StrategicAlloc.RRExists
