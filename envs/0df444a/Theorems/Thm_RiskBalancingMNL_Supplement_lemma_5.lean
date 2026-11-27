-- Prove2me | Theorems.Thm_RiskBalancingMNL_Supplement_lemma_5
-- name    : RiskBalancingMNL.Supplement.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:57:31.821203+00:00
-- url     : https://prove2.me/theorems/a4967ced-babc-59ab-a6b9-c80c57606009
-- title:
--   Lemma 5 — $\theta\ge[(1/\lambda-1)\pi]^2\ge0$ at every optimum
-- statement:
--   Consider the MNL model with asymmetric price sensitivities $\hat b_i>0$ and a risk weight $\lambda\in(0,1)$. Let $m$ be an optimal markup vector of problem (6), with expected profit $\pi$, and let $\theta=(\pi/\lambda)^2+2\sum_i(m_i-\pi/\lambda)q_i/(\hat b_iq_0)$ be evaluated at $m$. Then
--   $$
--   \theta\ \ge\ \Big[\Big(\frac1\lambda-1\Big)\pi\Big]^2\ \ge\ 0 .
--   $$
--   Nonnegativity of $\theta$ makes the square root in Theorem 2 real, and it orders the markups in Theorem 3.
--
--   **Formalization Note** Optimality is over all markup vectors with $\pi\ge0$. Assumption 1 is not assumed.
--
--   Differences from the source:
--   - generalization: Lemma 5 under Assumption 1, standing for the rest of §5 → at every optimal markup vector, without Assumption 1; reason: at an optimum θ = π²/λ² − 2π²/λ + g and g ≥ π², which gives the bound without Assumption 1; the source's case is the special case satisfying it
--   - reading: λ ∈ [0, 1) (problem (5)) → 0 < λ < 1; reason: θ contains π/λ, undefined at λ = 0
--   - encoding: problem (6) over share vectors q → IsOptimal over all markup vectors m ∈ ℝⁿ with π(m) ≥ 0; reason: the paper's one-to-one map between markups and shares (p.9), as in the published base mission
--   - encoding: primitives a_i, y_i, b, β of (16) → reduced form â_i, b̂_i > 0, c_i; reason: the primitives enter only through â_i = a_i + y_i and b̂_i = b − βy_i, and every positive b̂ arises
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §5.1, Lemma 5, p.15

import Mathlib
import Definitions.Def_RiskBalancingMNL_Supplement_AsymParams

namespace RiskBalancingMNL.Supplement

/-- **Lemma 5**, Li & Webster, *Optimizing Risk-balancing Return under Discrete Choice Models*,
SSRN 3959428 (PDF of 2021-11-14), §5.1, p.15: `θ ≥ [(1/λ − 1)π]² ≥ 0`.

Stated at every optimal markup vector `m` of problem (6) for `λ ∈ (0, 1)`, with `π` and `θ`
evaluated at `m`.

**Formalization Note** `θ` is the printed expression of p.15 (`AsymParams.theta`). Assumption 1 is
not assumed. `λ > 0` because `θ` contains `π/λ`. -/
theorem lemma_5 {n : ℕ} (P : AsymParams n) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (m : Fin n → ℝ) (hm : P.IsOptimal lam m) :
    ((1 / lam - 1) * P.profit m) ^ 2 ≤ P.theta lam m ∧ 0 ≤ ((1 / lam - 1) * P.profit m) ^ 2 := by sorry

end RiskBalancingMNL.Supplement
