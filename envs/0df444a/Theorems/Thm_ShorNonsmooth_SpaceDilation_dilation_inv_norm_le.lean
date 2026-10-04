-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_dilation_inv_norm_le
-- name    : ShorNonsmooth.SpaceDilation.dilation_inv_norm_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T04:39:31.341112+00:00
-- url     : https://prove2.me/theorems/c8e39de9-1fca-4390-8770-b931b14bbd18
-- title:
--   The inverse space dilation `R_{1/a}(ξ)` is a contraction for `a ≥ 1`
-- statement:
--   Let `ξ` be a unit vector and let `a ≥ 1`. Then the space dilation with coefficient `1/a` along `ξ` does not increase the norm:
--
--   $$
--   \left\| R_{1/a}(\xi) \, v \right\| \le \| v \| \qquad \text{for every } v \in E_n.
--   $$
--
--   Indeed, writing $v = \gamma \xi + w$ with $w \perp \xi$ and $\|\xi\| = 1$, one has $R_{1/a}(\xi) v = \frac{\gamma}{a}\xi + w$, so by (3.4)
--
--   $$
--   \| R_{1/a}(\xi) v \|^2 = \frac{\gamma^2}{a^2} + \| w \|^2 \le \gamma^2 + \|w\|^2 = \| v \|^2,
--   $$
--
--   because $a \ge 1$.
--
--   **Why it matters.** In the SDG recursion (3.9) we have $B_{k+1} = B_k R_{1/\alpha_{k+1}}(\xi_{k+1})$ and $A_{k+1} = R_{\alpha_{k+1}}(\xi_{k+1}) A_k$. Since every coefficient satisfies $\alpha > 1$, each factor of $B_k = A_k^{-1}$ is a contraction, so $\|B_k\|_{\mathrm{op}} \le 1$. Consequently
--
--   $$
--   \| x_k - x^* \| = \| B_k\, A_k (x_k - x^*) \| \le \| A_k (x_k - x^*) \|.$$
--
--   Thus the statement $\|A_k (x_k - x^*)\| \le d$ of Theorem 3.3 immediately implies that every iterate lies in $S_d = \{x : \|x - x^*\| \le d\}$, which is what permits condition (3.18) to be used at every step of the induction. This is the book's step on p. 56.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 51-52, formula (3.9) and Theorem 3.3, p. 56-57.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- For a unit vector `ξ` and `1 ≤ a`, the inverse dilation `R_{1/a}(ξ)` is a contraction:
`‖dilation (1/a) ξ v‖ ≤ ‖v‖` for every `v`.

This is formula (3.4) read with coefficient `1/a ≤ 1`: since `‖ξ‖ = 1`, for
`v = γ ξ + w` with `w ⟂ ξ` one has `R_{1/a}(ξ) v = (γ/a) ξ + w`, so

`‖R_{1/a}(ξ) v‖² = γ²/a² + ‖w‖² ≤ γ² + ‖w‖² = ‖v‖²`.

It is the operator-norm fact that closes the proof of Theorem 3.3. Because
`B_{k+1} = B_k R_{1/α_{k+1}}(ξ_{k+1})` and every coefficient `α > 1`, the accumulated
`B_k = A_k⁻¹` has operator norm at most `1`, whence

`‖x_k - x*‖ = ‖B_k (A_k (x_k - x*))‖ ≤ ‖A_k (x_k - x*)‖`.

So membership of the iterate in `S_d = {x : ‖x - x*‖ ≤ d}` follows from the distance
invariant instead of having to be assumed, which is what lets condition (3.18) be applied
at every iterate. -/
theorem dilation_inv_norm_le {n : ℕ} (a : ℝ) (ha : 1 ≤ a)
    (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖dilation (1 / a) ξ v‖ ≤ ‖v‖ := by
  sorry

end ShorNonsmooth.SpaceDilation
