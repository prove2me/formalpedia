-- Prove2me | Theorems.Thm_SennottDP_Tauberian_geometric_series
-- name    : SennottDP.Tauberian.geometric_series
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T13:01:33.944349+00:00
-- url     : https://prove2.me/theorems/8e1d1a5a-7e03-498c-9961-e5562143f7b9
-- title:
--   Remark A.3.3 — the geometric series: R = 1, sum B/(1−α), and Σ nα^n B = Bα/(1−α)^2
-- statement:
--   Let $B$ be a finite positive constant and take the constant sequence $u_n \equiv B$. The resulting geometric series has radius of convergence $R = 1$, and for every $\alpha \in [0,1)$
--   $$U(\alpha) = B(1 + \alpha + \alpha^2 + \cdots) = \frac{B}{1-\alpha}, \qquad B(\alpha + 2\alpha^2 + 3\alpha^3 + \cdots) = \frac{B\alpha}{(1-\alpha)^2}.$$
--
--   These closed forms are the basic examples of Abel means: $(1-\alpha)U(\alpha) = B$ for every $\alpha < 1$.
--
--   **Formalization Note** $B \in \mathbb{R}_{\ge 0}$ with $B > 0$; all sums are in $[0,\infty]$, and $1-\alpha$ is computed in $[0,\infty]$, where it is exact since $\alpha < 1$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 280, Remark A.3.3, (A.24)–(A.25)

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 280, Remark A.3.3: for the geometric series `u_n ≡ B` with `B` finite and
positive, the radius of convergence is `R = 1`, and for `α ∈ [0, 1)`
(A.24) `U(α) = B(1 + α + α² + …) = B/(1 − α)` and
(A.25) `B(α + 2α² + 3α³ + …) = Bα/(1 − α)²`. -/
theorem geometric_series (B : ℝ≥0) (hB : 0 < B) :
    radius (fun _ => (B : ℝ≥0∞)) = 1 ∧
      ∀ α : ℝ≥0, α < 1 →
        U (fun _ => (B : ℝ≥0∞)) α = (B : ℝ≥0∞) / (1 - (α : ℝ≥0∞)) ∧
          ∑' n : ℕ, (B : ℝ≥0∞) * (n : ℝ≥0∞) * (α : ℝ≥0∞) ^ n
            = (B : ℝ≥0∞) * (α : ℝ≥0∞) / (1 - (α : ℝ≥0∞)) ^ 2 := by sorry

end SennottDP.Tauberian
