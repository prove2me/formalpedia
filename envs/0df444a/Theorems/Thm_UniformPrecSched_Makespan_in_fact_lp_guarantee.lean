-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_in_fact_lp_guarantee
-- name    : UniformPrecSched.Makespan.in_fact_lp_guarantee
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:32:42.446571+00:00
-- url     : https://prove2.me/theorems/d2f76b93-a7ec-4fec-b27d-68fad494a4e2
-- title:
--   §3, p. 10 ("In fact") — from any feasible LP solution of value D, a schedule of length ≤ min{K + 2√K + 1, 1.89 log m + O(√log m)}D
-- statement:
--   There is an absolute constant $c$ with the following property. Let $I$ be an instance of $Q|prec|C_{\max}$ with $m \ge 2$ machines and $K$ distinct machine speeds, and let $(x, C, D)$ be any feasible solution of LP for $I$. Then $I$ has a feasible schedule $\sigma$ with
--   $$C_{\max}(\sigma) \le \min\bigl\{K + 2\sqrt K + 1,\ 1.89\log_2 m + c\sqrt{\log_2 m}\bigr\}\, D.$$
--
--   The paper uses this form, relative to an arbitrary feasible LP solution rather than to an optimal schedule, in its next section.
--
--   **Formalization Note** $\log m$ is $\log_2 m$, as the paper specifies; $m \ge 2$ keeps $\log_2 m \ge 1$ (at $m = 1$ the second branch would be $0$). The $O(\sqrt{\log m})$ term is one absolute constant $c$, chosen before the instance. The statement asserts existence of the schedule; the polynomial-time algorithm that finds it is not formalized.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 10, paragraph after Theorem 3.7 ("In fact, we have shown …")

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP

namespace UniformPrecSched.Makespan

/-- §3, p. 10 ("In fact"): there is an absolute constant `c` such that for every instance with
`m ≥ 2` machines and every feasible solution of `LP` with objective value `D`, there is a feasible
schedule of length at most `min{K + 2√K + 1, 1.89 log₂ m + c √(log₂ m)} · D`, where `K` is the
number of distinct machine speeds. -/
theorem in_fact_lp_guarantee :
    ∃ c : ℝ, ∀ (n m : ℕ) (I : Instance n m), 2 ≤ m →
      ∀ x C D, LPFeasible I x C D →
        ∃ σ : Schedule I, σ.makespan ≤
          min ((numSpeeds I : ℝ) + 2 * Real.sqrt (numSpeeds I) + 1)
              (1.89 * Real.logb 2 m + c * Real.sqrt (Real.logb 2 m)) * D := by sorry

end UniformPrecSched.Makespan
