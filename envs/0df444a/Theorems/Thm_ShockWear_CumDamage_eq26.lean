-- Prove2me | Theorems.Thm_ShockWear_CumDamage_eq26
-- name    : ShockWear.CumDamage.eq26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:47:51.36405+00:00
-- url     : https://prove2.me/theorems/ea733955-30dd-41f6-8090-87cd3cc5c7dc
-- title:
--   (2.6) — $\bar H(t) \ge \bar H(0) e^{-\lambda t}$ for all $t \ge 0$
-- statement:
--   Let $\lambda > 0$ and let $\bar P_0, \bar P_1, \dots$ satisfy (2.2): $1 \ge \bar P_0 \ge \bar P_1 \ge \dots \ge 0$. Let $\bar H$ be the shock survival function
--   $$\bar H(t) = \sum_{k=0}^\infty \bar P_k\, e^{-\lambda t}\frac{(\lambda t)^k}{k!}, \qquad t \ge 0.$$
--   Then
--   $$\bar H(t) \ge \bar H(0)\, e^{-\lambda t} \qquad \text{for all } t \ge 0.$$
--
--   This is display (2.6) of the paper, which it derives from the bound $r(t) \le \lambda$ on the hazard rate; it is used in the proof of Theorem 3.1 (3.4) to dispose of the exponentials $e^{-\theta t}$ with $\theta \ge \lambda$.
--
--   **Formalization Note** The paper says the $\bar P_k$ are probabilities; we state $\bar P_k \ge 0$ explicitly together with (2.2).
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 629, (2.6)

import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model

namespace ShockWear.CumDamage

open MeasureTheory ProbabilityTheory

theorem eq26 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 ≤ 1) (hanti : Antitone P)
    (hnn : ∀ k, 0 ≤ P k) :
    ∀ t, 0 ≤ t → shockSurv lam P 0 * Real.exp (-(lam * t)) ≤ shockSurv lam P t := by sorry

end ShockWear.CumDamage
