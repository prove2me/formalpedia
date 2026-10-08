-- Prove2me | Theorems.Thm_RevenueOrdered_Tightness_tightRevenue_sorted
-- name    : RevenueOrdered.Tightness.tightRevenue_sorted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:18:11.622689+00:00
-- url     : https://prove2.me/theorems/d37ee4c1-30d0-46a5-a1d7-0b0dcf22a637
-- title:
--   Theorem 3.4 proof, p. 10 — the tight instance has $k$ distinct revenues $r_i=\varepsilon^{-i}$
-- statement:
--   In the tight instance with $0<\varepsilon\le\tfrac12$, product $(i,j)$ has revenue $\varepsilon^{-j}>0$. The revenue function takes exactly $k$ distinct values, and, sorting them increasingly as $r_1<\dots<r_k$,
--   $$
--   r_i=\varepsilon^{-i}\qquad\text{for each } i\in[k].
--   $$
--
--   **Formalization Note** The sorted revenues are indexed from $0$, so the Lean statement reads $r_{i}=\varepsilon^{-(i+1)}$ for $i\in\{0,\dots,k-1\}$, after transporting the index along $\#\{\text{distinct revenues}\}=k$.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 10, proof of Theorem 3.4 ("we have r_i = ε^{−i} for each i ∈ [k]")

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

namespace RevenueOrdered.Tightness

/-- The revenues of the tight instance (p. 10): every revenue is positive, there are exactly
`k` distinct revenues, and `r_i = ε^{-i}` for each `i ∈ [k]` (0-based index `i` here stands for
the paper's `i + 1`). -/
theorem tightRevenue_sorted (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ x : TightProduct k, 0 < tightRevenue k ε x) ∧
      ∃ h : numRevenues (tightRevenue k ε) = k,
        ∀ i : Fin k, sortedRevenue (tightRevenue k ε) (Fin.cast h.symm i) = (ε ^ (i.val + 1))⁻¹ := by sorry

end RevenueOrdered.Tightness
