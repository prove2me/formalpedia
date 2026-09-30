-- Prove2me | Theorems.Thm_VeinottWagnerSS_RenewalCost_eq8_LAlpha_interchange
-- name    : VeinottWagnerSS.RenewalCost.eq8_LAlpha_interchange
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T13:07:05.496824+00:00
-- url     : https://prove2.me/theorems/5e82805b-4c39-4e8b-8396-0a11e7a6b104
-- title:
--   Eq. (8) — $L_\alpha(x, d) = G_\alpha(x) + \sum_{j=0}^{d} G_\alpha(x - j)\, m_\alpha(j)$
-- statement:
--   Let $\varphi$ be a demand distribution, $0 \le \alpha \le 1$ with $\alpha\varphi(0) < 1$, and $G_\alpha : \mathbb Z \to \mathbb R$ arbitrary. For every integer $x$ and every $d = 0, 1, \dots$, the double series (7) defining $L_\alpha(x, d)$ converges absolutely, and interchanging the order of summation gives
--   $$L_\alpha(x, d) = G_\alpha(x) + \sum_{j=0}^{d} G_\alpha(x - j)\, m_\alpha(j),$$
--   where $m_\alpha(j) = \sum_{i \ge 1} \alpha^i \varphi^i(j)$.
--
--   This finite form is what makes $L_\alpha$ computable once $m_\alpha$ is known.
--
--   **Formalization Note** Absolute convergence is stated as summability over $i$ of $\sum_{k=0}^{d} |\alpha^i G_\alpha(x-k)\varphi^i(k)|$ (the inner sum is finite). $L_\alpha$ is defined by the series (7).
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 533, Eq. (8)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_VeinottWagnerSS_RenewalCost_RenewalFunctions

namespace VeinottWagnerSS.RenewalCost

/-- Veinott & Wagner (1965), Eq. (8), p. 533: under `0 ≤ α ≤ 1` and `α φ(0) < 1`, the double
series (7) defining `L_α(x, d)` converges absolutely, and interchanging the order of summation
gives `L_α(x, d) = G_α(x) + ∑_{j=0}^{d} G_α(x − j) m_α(j)`. -/
theorem eq8_LAlpha_interchange (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hφ0 : α * D.φ 0 < 1) (G : ℤ → ℝ) (x : ℤ) (d : ℕ) :
    Summable (fun i : ℕ => ∑ k ∈ Finset.range (d + 1),
        |α ^ (i + 1) * G (x - (k : ℤ)) * convPow D.φ (i + 1) k|) ∧
      LAlpha D.φ α G x d =
        G x + ∑ j ∈ Finset.range (d + 1), G (x - (j : ℤ)) * mAlpha D.φ α j := by sorry

end VeinottWagnerSS.RenewalCost
