-- Prove2me | Theorems.Thm_RobustLP_Counterpart_rc_violation_implies_deviation
-- name    : RobustLP.Counterpart.rc_violation_implies_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:27:05.109984+00:00
-- url     : https://prove2.me/theorems/5e32a4f2-eca0-4c5f-a248-2ccba9d094cb
-- title:
--   Proof of Proposition 1: a violated perturbed constraint forces $\sum_{j\in J_i}\xi_{ij}a_{ij}z_{ij} > \Omega\sqrt{\sum_{j\in J_i}a_{ij}^2z_{ij}^2}$
-- statement:
--   Let an uncertain linear program with uncertain-entry sets $J_i$ be given, and let $\epsilon>0$, $\delta>0$, $\Omega>0$. Let $(x,y,z)$ be feasible for the robust counterpart (RC[ε, δ, Ω]). Fix a row $i$ and a vector $(\xi_{ij})_j$ with $\xi_{ij}=0$ for $j\notin J_i$ and $|\xi_{ij}|\le1$ for all $j$. If the perturbed $i$-th constraint is violated beyond the tolerance,
--   $$
--   \sum_j (1+\epsilon\xi_{ij})\,a_{ij}x_j > b_i + \delta\max[1,|b_i|],
--   $$
--   then
--   $$
--   \sum_{j\in J_i}\xi_{ij}\,a_{ij}\,z_{ij} > \Omega\sqrt{\sum_{j\in J_i}a_{ij}^2 z_{ij}^2}.
--   $$
--
--   This deterministic implication is the chain of inequalities in the proof of Proposition 1: it reduces the violation event of row $i$ to a large-deviation event for the weighted sum $\sum_{j}\xi_{ij}p_j$ with $p_j = a_{ij}z_{ij}$, to which Eq. (1) applies.
--
--   **Formalization Note** Stated in corrected form. The printed chain contains the misprints $(x_i - y_{ij})$ for $(x_j - z_{ij})$ and, in its last line, $\xi_{ij}|a_{ij}|y_j$ and $a_{ij}^2y_{ij}^2$ for $\xi_{ij}|a_{ij}|z_{ij}$ and $a_{ij}^2 z_{ij}^2$; its first equality replaces $\xi_{ij}a_{ij}$ by $\xi_{ij}|a_{ij}|$, which holds only in distribution. The statement here keeps $a_{ij}$ and is a pointwise implication, valid for every realization. The degenerate case $\sum_{j\in J_i}a_{ij}^2z_{ij}^2 = 0$ is not excluded.
-- source:
--   Ben-Tal and Nemirovski, Robust solutions of Linear Programming problems contaminated with uncertain data, Math. Program. Ser. A 88 (2000) 411–424, p. 419, §3.1, proof of Proposition 1 (displayed chain of probabilities), corrected

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP
import Definitions.Def_RobustLP_Counterpart_RobustCounterparts

namespace RobustLP.Counterpart

/-- **Proof of Proposition 1, displayed chain** (Ben-Tal–Nemirovski 2000, §3.1, p. 419), in
corrected pointwise form. Let `ε > 0`, `δ > 0`, `Ω > 0` and let `(x, y, z)` be feasible for
(RC[ε, δ, Ω]). Fix a row `i` and a realization `ξi` of the perturbations of that row, with
`ξi j = 0` for `j ∉ J i` and `|ξi j| ≤ 1`. If the perturbed constraint
`∑_j (1 + ε ξi_j) a_{ij} x_j > b_i + δ max[1, |b_i|]` is violated, then
`∑_{j ∈ J_i} ξi_j a_{ij} z_{ij} > Ω √(∑_{j ∈ J_i} a_{ij}² z_{ij}²)`. -/
theorem rc_violation_implies_deviation {n p m : ℕ} (L : UncertainLP n p m)
    (ε δ Ω : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hΩ : 0 < Ω)
    (x : Fin n → ℝ) (y z : Fin m → Fin n → ℝ) (hRC : L.RCFeasible ε δ Ω x y z)
    (i : Fin m) (ξi : Fin n → ℝ) (hξ0 : ∀ j ∉ L.J i, ξi j = 0) (hξ1 : ∀ j, |ξi j| ≤ 1)
    (hviol : L.bPlus δ i < ∑ j, (1 + ε * ξi j) * L.A i j * x j) :
    Ω * Real.sqrt (∑ j ∈ L.J i, L.A i j ^ 2 * z i j ^ 2) <
      ∑ j ∈ L.J i, ξi j * L.A i j * z i j := by sorry

end RobustLP.Counterpart
