-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_lyapunov_init_centered
-- name    : SAGFiniteSum.Rate.lyapunov_init_centered
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:39.900015+00:00
-- url     : https://prove2.me/theorems/03a0e2bf-2a48-4e4d-8436-df181f2c817d
-- title:
--   App. B.8.2, pp. 47–48 — with y⁰ᵢ = f′ᵢ(x⁰) − g′(x⁰): ℒ(θ⁰) ≤ (3/2)(g(x⁰) − g(x*)) + (4L/n)‖x⁰ − x*‖²
-- statement:
--   Assume the standing assumptions of §3 with $n\ge2$, and let $\mathcal L$ be the Lyapunov function with the constants of App. B.5. For the initial state $\theta^0=(y^0,x^0)$ with the centered table $y^0_i=f'_i(x^0)-g'(x^0)$,
--   $$
--   \mathcal L(\theta^0)\ \le\ \frac32\big(g(x^0)-g(x^*)\big)+\frac{4L}{n}\|x^0-x^*\|^2 .
--   $$
--
--   This is Theorem 1's constant $C_0$ for the centered initialization.
--
--   **Formalization Note** The page's intermediate identity on p. 47 writes the coefficient of $\|y^0-f'(x^*)\|^2$ as $\frac1{16nL}(1-\frac2n)$, while $a_2=\frac1{16nL}(1-\frac1{2n})$; that identity is not stated. The final inequality holds with the correct $a_2$, since $1-\frac2n+\frac12(1-\frac1{2n})\le\frac32$. The page also writes "$y^0_i=y^0_i=$" (a doubled symbol) and $L(\theta^0)$ for $\mathcal L(\theta^0)$ in the last display.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.8.2, pp. 47–48

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model
import Definitions.Def_SAGFiniteSum_Rate_Lyapunov

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- B.8.2, initial value (arXiv:1309.2388v2, pp. 47–48). With the B.5 constants and `n ≥ 2`, the
initial value of the Lyapunov function at `θ⁰ = (y⁰, x⁰)` with the centered table
`y⁰ᵢ = f'ᵢ(x⁰) − g'(x⁰)` satisfies `ℒ(θ⁰) ≤ (3/2)(g(x⁰) − g(x*)) + (4L/n)‖x⁰ − x*‖²`. -/
theorem lyapunov_init_centered {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar) (hn : 2 ≤ n)
    (x0 : EuclideanSpace ℝ (Fin p)) :
    sagLyap f f' L xstar (centeredTable f' x0, x0)
      ≤ 3 / 2 * (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar)
        + 4 * L / (n : ℝ) * ‖x0 - xstar‖ ^ 2 := by sorry

end SAGFiniteSum.Rate
