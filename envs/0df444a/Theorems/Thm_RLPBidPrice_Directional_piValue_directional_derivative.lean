-- Prove2me | Theorems.Thm_RLPBidPrice_Directional_piValue_directional_derivative
-- name    : RLPBidPrice.Directional.piValue_directional_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T13:12:24.253364+00:00
-- url     : https://prove2.me/theorems/901a8f59-d459-44ec-b02a-58807431ed5c
-- title:
--   Proof of Proposition 2, p. 212 — D(x, Y; d) = lim_{h↓0} (1/h)[v(x + hd, Y) − v(x, Y)] = inf{dᵀμ : μ ∈ ∂v(x, Y)}
-- statement:
--   Let $A$ be a 0/1 incidence matrix with nonzero columns, $r \ge 0$, $x$ a capacity vector with every component $x^i > 0$, and $Y \ge 0$ a demand vector. For every direction $d \in \mathbb{R}^m$ the one-sided directional derivative of $z \mapsto v(z, Y)$ at $x$ exists and equals the least value of $d^\top \mu$ over the superdifferential:
--   $$D(x, Y; d) = \lim_{h \downarrow 0} \frac{1}{h}\big[v(x + hd, Y) - v(x, Y)\big] = \inf\{d^\top \mu : \mu \in \partial v(x, Y)\},$$
--   where $\partial v(x, Y) = \{\mu : v(z, Y) \le v(x, Y) + \mu^\top (z - x) \text{ for all } z \ge 0\}$.
--
--   The paper cites this as a known fact about concave functions (Bazaraa, Sherali and Shetty 1993, p. 218) and applies it to the LP value in each demand scenario.
--
--   **Formalization Note.** The limit is one-sided, $h \to 0^+$ (`nhdsWithin 0 (Set.Ioi 0)`): the two-sided limit written in the paper as $\lim_{h \to 0}$ does not exist in the nondifferentiable case this section treats (one leg, one itinerary, $r = 1$, $x = 1$, $Y = 1$, $d = 1$: the right quotient is $0$, the left one is $1$). For small $h > 0$, $x + hd \ge 0$ because $x > 0$. The infimum is a real `sInf`; for $x > 0$ the superdifferential is nonempty and bounded, so it is an attained minimum. The time index $k$ is dropped.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 212, proof of Proposition 2, display (citing Bazaraa, Sherali, Shetty 1993, p. 218)

import Mathlib
import Definitions.Def_RLPBidPrice_Directional_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Directional

/-- Proof of Proposition 2, p. 212 (Bazaraa–Sherali–Shetty): at `x > 0` the one-sided
directional derivative of `z ↦ v(z, y₀)` in the direction `d` exists and equals
`inf { dᵀμ : μ ∈ ∂v(x, y₀) }`. -/
theorem piValue_directional_derivative {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin n → ℝ) (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : ∀ i, 0 < x i)
    (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) (d : Fin m → ℝ) :
    Filter.Tendsto (fun h : ℝ => h⁻¹ * (piValue A r (x + h • d) y₀ - piValue A r x y₀))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sInf ((fun μ : Fin m → ℝ => d ⬝ᵥ μ) '' superdiff A r x y₀))) := by sorry

end RLPBidPrice.Directional
