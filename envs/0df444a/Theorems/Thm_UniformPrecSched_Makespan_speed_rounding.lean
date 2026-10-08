-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_speed_rounding
-- name    : UniformPrecSched.Makespan.speed_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:32:48.411184+00:00
-- url     : https://prove2.me/theorems/36676b91-2148-4b9d-9a05-52a464bfb155
-- title:
--   §3, p. 10 — rounding leaves ⌊log_β(αm)⌋ + 1 speeds and raises the LP value by at most β(1 + 1/α)
-- statement:
--   Let $I$ be an instance of $Q|prec|C_{\max}$ with $m$ machines and fastest speed $\bar s_1$, let $\alpha \ge 1$ and $\beta > 1$, and let $I'$ be obtained by rounding all speeds less than $\bar s_1/(\alpha m)$ down to $0$ and all speeds in $(\bar s_1\beta^{-k}, \bar s_1\beta^{-k+1}]$ down to $\bar s_1\beta^{-k}$. Then
--
--   1. $I'$ has at most $\lfloor \log_\beta(\alpha m)\rfloor + 1$ distinct speeds;
--   2. for every feasible solution of LP for $I$ with objective value $D$ there is a feasible solution of LP for $I'$ with objective value $D'$ satisfying
--   $$D' \le \beta\Bigl(1 + \frac1\alpha\Bigr) D.$$
--
--   With $\beta = e$ and $\alpha = \log_2 m$ this turns Corollary 3.6 into the $1.89\log_2 m + O(\sqrt{\log m})$ branch of Theorem 3.7.
--
--   **Formalization Note** The page says "there are $\log_\beta(\alpha m)$ distinct speeds resulting"; the rounding can produce $\lfloor\log_\beta(\alpha m)\rfloor + 1$ (for instance one speed when $\alpha m = 1$), which is the bound stated here. The paper normalizes $\bar s_1 = 1$; here the rounding is relative to $\bar s_1$. "Increases the optimal value by at most a factor" is stated through feasible solutions, which implies it for optimal ones.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 10, §3 (general rounding with β > 1, α ≥ 1); p. 9 for the case α = 1, β = 2

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP
import Definitions.Def_UniformPrecSched_Makespan_Rounding

namespace UniformPrecSched.Makespan

/-- §3, p. 10: for `α ≥ 1` and `β > 1`, rounding the speeds less than `s̄_1/(αm)` down to `0` and
the speeds in `(s̄_1 β^{-k}, s̄_1 β^{-k+1}]` down to `s̄_1 β^{-k}` leaves at most
`⌊log_β(αm)⌋ + 1` distinct speeds (the page says `log_β(αm)`), and turns every feasible solution
of `LP` with objective value `D` into a feasible solution of `LP` for the rounded instance with
objective value at most `β(1 + 1/α) D`. -/
theorem speed_rounding {n m : ℕ} (I : Instance n m) (α β : ℝ) (hα : 1 ≤ α) (hβ : 1 < β) :
    (numSpeeds (roundInstance I α β hα hβ) : ℝ) ≤ (⌊Real.logb β (α * m)⌋ : ℝ) + 1 ∧
      ∀ x C D, LPFeasible I x C D →
        ∃ x' C' D', LPFeasible (roundInstance I α β hα hβ) x' C' D' ∧
          D' ≤ β * (1 + 1 / α) * D := by sorry

end UniformPrecSched.Makespan
