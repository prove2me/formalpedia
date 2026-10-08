-- Prove2me | Theorems.Thm_PowerTwoChoices_Limit_theorem_2
-- name    : PowerTwoChoices.Limit.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:07.825205+00:00
-- url     : https://prove2.me/theorems/f8bfb0b8-9355-4ab2-901c-18ee0c97a29b
-- title:
--   Theorem 2 — the tails decrease doubly exponentially, uniformly in $t$; from empty, $s_i(t)\le\pi_i$
-- statement:
--   Let $d\ge2$, $0<\lambda<1$, and let $s(t)$ be a trajectory of the limiting supermarket system (1), with fixed point $\pi_i=\lambda^{(d^i-1)/(d-1)}$.
--
--   1. If $s_j(0)=0$ for some $j$, then there are constants $N\ge1$, $0<\alpha<1$, $\beta>1$, $\gamma>0$, independent of $t$, such that
--   $$s_i(t)\le\gamma\,\alpha^{\beta^i}\qquad\text{for all }t\ge0\text{ and all }i\ge N,$$
--   that is, the sequence $(s_i(t))_{i\ge0}$ decreases doubly exponentially (Definition 1) for all $t\ge0$ with the same constants.
--   2. If the system begins empty ($s_0(0)=1$, $s_i(0)=0$ for $i\ge1$), then $s_i(t)\le\pi_i$ for all $t\ge0$ and all $i$.
--
--   The theorem is an invariant of the dynamics: it bounds how far the tails can be from the fixed point at any time, and it is what makes the expected time in the system finite along the trajectory.
--
--   **Formalization Note.** The constants are quantified after the trajectory and before $t$. $N$ is a natural number.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, p. 1097, Theorem 2 (with Definition 1, p. 1097)

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

open scoped ENNReal
open Filter Topology

namespace PowerTwoChoices.Limit

/-- Theorem 2 (Mitzenmacher 2001, p. 1097). Let `d ≥ 2` and `0 < λ < 1`.
(a) If `s_j(0) = 0` for some `j`, then the sequences `(s_i(t))_i` decrease doubly
exponentially for all `t ≥ 0`, with constants `N, α, β, γ` (Definition 1) independent of `t`.
(b) If the system begins empty, then `s_i(t) ≤ π_i` for all `t ≥ 0` and all `i`. -/
theorem theorem_2 (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s → (∃ j : ℕ, s 0 j = 0) →
      ∃ (N : ℕ) (α β γ : ℝ), ∀ t : ℝ, 0 ≤ t → IsDoublyExpBound N α β γ (s t)) ∧
    (∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s → s 0 = emptyState →
      ∀ t : ℝ, 0 ≤ t → ∀ i : ℕ, s t i ≤ fixedPoint lam d i) := by sorry

end PowerTwoChoices.Limit
