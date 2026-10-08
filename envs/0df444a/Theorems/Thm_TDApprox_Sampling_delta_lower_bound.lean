-- Prove2me | Theorems.Thm_TDApprox_Sampling_delta_lower_bound
-- name    : TDApprox.Sampling.delta_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:44.640415+00:00
-- url     : https://prove2.me/theorems/c19e9ad1-0a2b-4b87-bf16-4c418c898d9a
-- title:
--   §9, p. 25 — positive lower bound on the growth coefficient
-- statement:
--   Suppose $0<\alpha<1$, $p_1,p_2\ge0$, $p_1+p_2\le1$, $p_2>5/(6\alpha)$, and $0\le q_2\le q_1$ with $q_1>0$. For the coefficient $\Delta$ in the specialized mean recurrence,
--
--   $$\Delta\ge(6\alpha p_2-5)q_1>0.$$
--
--   Thus the mean update has a strictly positive growth factor whenever the step size is positive. The result isolates the paper's numerical threshold $5/6$.
--
--   **Formalization Note** The explicit value $\varepsilon=6\alpha p_2-5$ witnesses the paper's assertion that some positive $\varepsilon$ exists.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Theorem 3 proof, p. 25, Δ_t lower bound; https://dspace.mit.edu/entities/publication/ab395d25-a6d3-407a-9589-60eaac58fd05

import Mathlib
import Definitions.Def_TDApprox_Sampling_Model

namespace TDApprox.Sampling

theorem delta_lower_bound
    (α p₁ p₂ q₁ q₂ : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hpsum : p₁ + p₂ ≤ 1)
    (hpbig : 5 / (6 * α) < p₂)
    (hq₂ : 0 ≤ q₂) (hqle : q₂ ≤ q₁) (hq₁ : 0 < q₁) :
    (6 * α * p₂ - 5) * q₁ ≤
        (α * p₁ + 2 * α * p₂ - 1) * q₁ +
          2 * (α * p₁ + 2 * α * p₂ - 2) * q₂ ∧
      0 < 6 * α * p₂ - 5 := by sorry

end TDApprox.Sampling
