-- Prove2me | Theorems.Thm_ShockWear_CumDamage_corollary42
-- name    : ShockWear.CumDamage.corollary42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:48:49.999986+00:00
-- url     : https://prove2.me/theorems/336ca814-b57b-4a83-b282-f05a89348b8c
-- title:
--   Corollary 4.2 (4.7) — under Poisson shocks with i.i.d. nonnegative cumulative damage, the life distribution is IHRA
-- statement:
--   Shocks arrive according to a Poisson process of rate $\lambda > 0$. The $i$th shock causes a damage $X_i$; the damages are independent with common distribution function $F$, where $F(z) = 0$ for all $z < 0$. Damage accumulates additively, and the item survives $k$ shocks if $X_1 + \dots + X_k$ does not exceed the threshold $x$, which happens with probability $F^{(k)}(x)$ ($F^{(0)}$ is degenerate at $0$). Then the survival function
--   $$\bar H(t) = \sum_{k=0}^\infty e^{-\lambda t}\frac{(\lambda t)^k}{k!}\, F^{(k)}(x)$$
--   is IHRA: $[\bar H(t)]^{1/t}$ is decreasing in $t > 0$.
--
--   This is the first statement of Corollary 4.2. Its point, in the authors' words, is that the IHRA property is obtained "as an implication of a natural physical model. The only hypothesis imposed upon $F$ is that it be the distribution of a nonnegative random variable."
--
--   **Formalization Note** $F$ is a probability measure $\mu$ on $\mathbb R$ with $\mu(-\infty,0) = 0$ and no other restriction; $F^{(k)}(x)$ is the mass of $(-\infty, x]$ under the $k$-fold convolution of $\mu$; $\bar H$ is the series (2.1), equal to $1$ for $t < 0$. The threshold $x$ ranges over all reals as printed (for $x < 0$, $\bar H \equiv 0$ on $[0,\infty)$). IHRA is stated with the real power $[\bar H(t)]^{1/t}$.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), pp. 637–638, Corollary 4.2, first statement, display (4.7)

import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model

namespace ShockWear.CumDamage

open MeasureTheory ProbabilityTheory

theorem corollary42 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (lam : ℝ) (hlam : 0 < lam) (x : ℝ) :
    IsIHRA (shockSurv lam (fun k => cdfPow μ k x)) := by sorry

end ShockWear.CumDamage
