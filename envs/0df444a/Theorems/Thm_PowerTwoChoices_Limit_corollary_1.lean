-- Prove2me | Theorems.Thm_PowerTwoChoices_Limit_corollary_1
-- name    : PowerTwoChoices.Limit.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:03.037142+00:00
-- url     : https://prove2.me/theorems/a4b8fe21-722d-4a3c-a536-70657516029c
-- title:
--   Corollary 1 — the $L_1$ distance to the fixed point converges exponentially to $0$
-- statement:
--   Let $d\ge2$ and $0<\lambda<1$, and let $\pi_i=\lambda^{(d^i-1)/(d-1)}$ be the fixed point. There are constants $w_i\ge1$ ($i\ge1$), chosen before any trajectory, such that for every trajectory $s(t)$ of the limiting supermarket system (1) satisfying the conditions of Theorem 3, namely $\Phi(0)=\sum_{i\ge1}w_i|s_i(0)-\pi_i|<\infty$, or $s_j(0)=0$ for some $j$, the $L_1$ distance from the fixed point
--   $$D(t)=\sum_{i=1}^\infty|s_i(t)-\pi_i|$$
--   converges exponentially to $0$: there are $\delta>0$ and $c_0$ with $D(t)\le c_0e^{-\delta t}$ for all $t\ge0$.
--
--   Hence the limiting system quickly becomes extremely close to its fixed point from any such starting point.
--
--   **Formalization Note.** The paper calls the distance $d(t)$; it is renamed because $d$ is the number of choices. "Under the conditions of Theorem 3" refers to Theorem 3's weights, which the paper leaves as "appropriately chosen constants"; since they cannot be referred to across items, the weights are quantified existentially here, before the trajectory, with both of Theorem 3's conditions ($\Phi(0)<\infty$, and $s_j(0)=0$ for some $j$) as separate clauses. The second clause keeps the weights from being chosen so as to make the first vacuous. $D(t)$ and $\Phi(0)$ are computed in $[0,\infty]$.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, p. 1098, Corollary 1

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

open scoped ENNReal
open Filter Topology

namespace PowerTwoChoices.Limit

/-- Corollary 1 (Mitzenmacher 2001, p. 1098). Let `d ≥ 2` and `0 < λ < 1`. Under the conditions
of Theorem 3 (weights `w_i ≥ 1` for `i ≥ 1`, fixed before any trajectory, with either
`Φ(0) = ∑_{i ≥ 1} w_i |s_i(0) - π_i| < ∞` or `s_j(0) = 0` for some `j`), the `L₁` distance
`∑_{i ≥ 1} |s_i(t) - π_i|` from the fixed point converges exponentially to `0` (Definition 2). -/
theorem corollary_1 (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ w : ℕ → ℝ, (∀ i : ℕ, 1 ≤ i → 1 ≤ w i) ∧
      ∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s →
        (potential lam d w (s 0) < ⊤ →
          ConvergesExponentially (fun t => l1Dist lam d (s t))) ∧
        ((∃ j : ℕ, s 0 j = 0) →
          ConvergesExponentially (fun t => l1Dist lam d (s t))) := by sorry

end PowerTwoChoices.Limit
