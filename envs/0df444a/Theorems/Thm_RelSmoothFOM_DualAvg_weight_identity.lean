-- Prove2me | Theorems.Thm_RelSmoothFOM_DualAvg_weight_identity
-- name    : RelSmoothFOM.DualAvg.weight_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:33.027985+00:00
-- url     : https://prove2.me/theorems/de692173-3920-4516-9af3-f5273cf51542
-- title:
--   Proof of Theorem 3.2, p. 348 — μ + (1/a_{k+1})(1 + μA_k) = (1 + μA_{k+1})/a_{k+1} = (1/a_{k+1})(L/(L−μ))^{k+1} = L
-- statement:
--   Let $0 \le \mu < L$, $a_{k+1} = \frac{1}{L-\mu}\left(\frac{L}{L-\mu}\right)^k$ and $A_k = \sum_{i=0}^{k-1} a_{i+1}$. Then for every $k \ge 0$,
--   $$\mu + \frac{1}{a_{k+1}}(1 + \mu A_k) = \frac{1 + \mu A_{k+1}}{a_{k+1}} = \frac{1}{a_{k+1}}\left(\frac{L}{L-\mu}\right)^{k+1} = L .$$
--
--   The weights of Algorithm 2 are chosen exactly so that this coefficient equals the relative smoothness constant $L$, which lets Definition 1.1 close the one-step recursion $\psi^*_{k+1} \ge \psi^*_k + a_{k+1} f(x^{k+1})$.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 348, proof of Theorem 3.2, first display line

import Mathlib
import Definitions.Def_RelSmoothFOM_DualAvg_Setting

namespace RelSmoothFOM.DualAvg

/-- Proof of Theorem 3.2, p. 348: for `0 ≤ μ < L` and every `k`,
`μ + (1/a_{k+1})(1 + μA_k) = (1 + μA_{k+1})/a_{k+1} = (1/a_{k+1})(L/(L − μ))^{k+1} = L`. -/
theorem weight_identity (L μ : ℝ) (hμ : 0 ≤ μ) (hμL : μ < L) (k : ℕ) :
    μ + 1 / daWeight L μ k * (1 + μ * daSum L μ k) =
        (1 + μ * daSum L μ (k + 1)) / daWeight L μ k ∧
      (1 + μ * daSum L μ (k + 1)) / daWeight L μ k =
        1 / daWeight L μ k * (L / (L - μ)) ^ (k + 1) ∧
      1 / daWeight L μ k * (L / (L - μ)) ^ (k + 1) = L := by sorry

end RelSmoothFOM.DualAvg
