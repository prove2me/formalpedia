-- Prove2me | Theorems.Thm_ProxBundle_GPB_proposition_4_3
-- name    : ProxBundle.GPB.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:27.932585+00:00
-- url     : https://prove2.me/theorems/ff1fceda-5a0f-4c0b-b77e-39905605470f
-- title:
--   Proposition 4.3, p. 14 — serious-iteration count
-- statement:
--   Let $x_0^*$ be a nearest minimizer to the initial point $x_0$, and put $d_0=\|x_0-x_0^*\|$. For the abstract serious iterates of GPB, let $K$ be the first positive index for which $\phi(\hat y_K)-\phi^*\le\bar\varepsilon$. Then $K$ exists and
--   $$
--   K\le\min\left\{\frac{d_0^2}{\lambda\bar\varepsilon},\frac{1}{\mu\lambda_\mu}\log\left(1+\frac{\mu d_0^2}{\bar\varepsilon}\right)\right\}+1,
--   \qquad \|\hat x_k-x_0^*\|\le\sqrt2\,d_0\quad(0\le k<K).
--   $$
--   The first bound controls the number of serious cycles; the second controls their starting distances.
--
--   **Formalization Note** When $\mu=0$, the second expression is interpreted as the first. The statement explicitly requires $K$ to be the first successful index.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, p. 14, Proposition 4.3, (47)–(48)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

namespace ProxBundle.GPB

/-- Proposition 4.3, p. 14: first successful serious iterate, count (47), and (48). -/
theorem proposition_4_3 {n : ℕ} (P : Instance n) (μ lam ε : ℝ)
    (x0 x0s : E n) (xh yh : ℕ → E n) (Γh : ℕ → E n → ℝ)
    (hμ : 0 ≤ μ) (hA1 : P.A1 μ) (hlam : 0 < lam) (hε : 0 < ε)
    (hhat : IsHat P μ lam ε x0 xh yh Γh)
    (hopt : P.IsNearestOpt x0 x0s) :
    ∃ K : ℕ, 1 ≤ K ∧
      P.φ (yh K) - P.φ x0s ≤ ε ∧
      (∀ i : ℕ, 1 ≤ i → i < K → ε < P.φ (yh i) - P.φ x0s) ∧
      (K : ℝ) ≤ serBound μ lam ε (‖x0 - x0s‖ ^ 2) + 1 ∧
      (∀ k : ℕ, k < K → ‖xh k - x0s‖ ≤ Real.sqrt 2 * ‖x0 - x0s‖) := by sorry

end ProxBundle.GPB
