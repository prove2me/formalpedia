-- Prove2me | Theorems.Thm_RLPBidPrice_Unbiased_lemma4_ae_gradient_exists
-- name    : RLPBidPrice.Unbiased.lemma4_ae_gradient_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T12:48:44.113218+00:00
-- url     : https://prove2.me/theorems/a1bf86af-ccb3-40b9-969b-e00d2ee32405
-- title:
--   Lemma 4 (corrected: C1 on [A I], independent demands) — ∇ₓv(x, Y) exists with probability one
-- statement:
--   Let $A$ be a 0/1 incidence matrix with nonzero columns, $r \ge 0$, and $x \ge 0$ satisfying Condition C1′. Let $Y = (Y^1, \dots, Y^n)$ be a random demand vector on a probability space $(\Omega, P)$: measurable, $Y \ge 0$ almost surely, with mutually independent components satisfying Condition 2 ($t \mapsto P(Y^j \le t)$ is continuous for every $j$). Then, with probability one, the perfect-information LP value $x' \mapsto v(x', Y) = \max\{r^\top y : Ay \le x',\ 0 \le y \le Y\}$ is differentiable at $x$:
--   $$P\big(\nabla_x v(x, Y) \text{ exists}\big) = 1.$$
--
--   This is the almost-sure differentiability that feeds Lemma 1 in the proof of Theorem 1.
--
--   **Formalization Note.** Differentiability is Fréchet differentiability of $x' \mapsto v(x', Y(\omega))$ at $x$. C1′ forces every $x^i \neq 0$, so with $x \ge 0$ the point $x$ is interior. Condition 2 is kept in the paper's marginal form (continuity of each distribution function); the alternative of a joint density is not assumed. The time index $k$ is dropped.
--
--   **Correction.** Two hypotheses are strengthened. (i) Condition 1 is applied to the columns of $[A\ I]$ (C1′): with $A$ having rows $(0,1,1), (1,1,0), (1,0,1)$, $r = (100,1,1)$, $x = (1,1,1)$ and $Y^j$ i.i.d. uniform on $[0,2]$, the printed Condition 1 and Condition 2 hold, but on $\{Y^1 > 1\}$ (probability $1/2$) the optimal dual prices form the segment $\{(0, t, 100 - t) : 1 \le t \le 99\}$, so $v(\cdot, Y)$ is not differentiable there. (ii) The components of $Y$ are assumed mutually independent: with one leg, $x = 1$, fares $(2, 1)$ and $Y^2 = 1 - Y^1$, $Y^1$ uniform on $[0,1]$, Conditions C1′ and 2 hold but $Y^1 + Y^2 = x$ surely and $v(\cdot, Y)$ has a kink at $x$ almost surely.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 211, Lemma 4

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Unbiased

theorem lemma4_ae_gradient_exists {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (hC1 : ConditionOnePrime A x)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hC2 : ConditionTwo P Y) (hind : ProbabilityTheory.iIndepFun (fun j ω => Y ω j) P) :
    ∀ᵐ ω ∂P, DifferentiableAt ℝ (fun x' => piValue A r x' (Y ω)) x := by sorry

end RLPBidPrice.Unbiased
