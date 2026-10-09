-- Prove2me | Theorems.Thm_RegLearnGames_FirstOrder_quadratic_inequality
-- name    : RegLearnGames.FirstOrder.quadratic_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:45:20.557294+00:00
-- url     : https://prove2.me/theorems/3a1f15af-e97b-438f-8918-fb873bd786fa
-- title:
--   Quadratic inequality, supp. p. 10 — cost bound after introducing x
-- statement:
--   In the finite cost game of Theorem 23, suppose costs lie in $[0,1]$, $0<\mu<1$, the game is $(\lambda,\mu)$-smooth, the play through $T\ge1$ is mixed, and the first-order bound (21) holds with $A_1\ge0$. Set
--   $$x=\sqrt{\lambda T\mathrm{OPT}'+\mu\sum_{t=1}^T C(w^t)}.$$
--   Then
--   $$\frac{x^2-\lambda T\mathrm{OPT}'}{\mu}\le x^2+A_1\sqrt{n\log d}\,x+A_2n\log d.$$
--
--   This is the paper's inequality from which its quadratic bound on $x$ follows.
--
--   **Formalization Note** The assumptions $0<\mu<1$ and $T\ge1$ make the theorem's divisions meaningful; $A_1\ge0$ is needed by the preceding Cauchy–Schwarz step. Smoothness and nonnegative costs imply that the expression under the square root is nonnegative. The paper writes both `log` and `ln`; both mean the natural logarithm.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, supp. p. 10 (PDF p. 19), quadratic display following equation (22)

import Mathlib
import Definitions.Def_RegLearnGames_FirstOrder_Setting

namespace RegLearnGames.FirstOrder

open Finset

/-- The quadratic inequality on the quantity `x` defined in Appendix H. -/
theorem quadratic_inequality {n d : ℕ} [NeZero d]
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (hc : ∀ i s, c i s ∈ Set.Icc (0 : ℝ) 1)
    (lam mu : ℝ) (hmu₀ : 0 < mu) (hmu₁ : mu < 1)
    (hsmooth : IsSmoothCost c lam mu)
    (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁)
    (T : ℕ) (hT : 1 ≤ T)
    (w : ℕ → Fin n → Fin d → ℝ)
    (hw : ∀ t ∈ Finset.Icc 1 T, AGT.IsMixedProfile (w t))
    (hreg : HasFirstOrderRegret c w T A₁ A₂) :
    let x : ℝ := Real.sqrt (lam * (T : ℝ) * optCost c +
      mu * (∑ t ∈ Finset.Icc 1 T, socialCost c (w t)))
    (1 / mu) * (x ^ 2 - lam * (T : ℝ) * optCost c) ≤
      x ^ 2 + A₁ * Real.sqrt ((n : ℝ) * Real.log (d : ℝ)) * x +
        A₂ * (n : ℝ) * Real.log (d : ℝ) := by sorry

end RegLearnGames.FirstOrder
