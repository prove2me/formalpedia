-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_rounded_schedule_lift
-- name    : UniformPrecSched.Makespan.rounded_schedule_lift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:32:31.975839+00:00
-- url     : https://prove2.me/theorems/b594bc2c-c550-4121-88aa-da1c0e6f6049
-- title:
--   §3, p. 9 — a schedule for the rounded instance is a schedule of no greater length for the original instance
-- statement:
--   Let $I$ be an instance of $Q|prec|C_{\max}$, $\alpha \ge 1$ and $\beta > 1$, and let $I'$ be the instance obtained by the speed rounding of §3 (machines of speed below $\bar s_1/(\alpha m)$ dropped, every other speed rounded down to the power $\bar s_1\beta^{-k}$ just below it). For every feasible schedule $\sigma'$ of $I'$ there is a feasible schedule $\sigma$ of $I$ that processes each job on the same (original) machine with the same start time, and
--   $$C_{\max}(\sigma) \le C_{\max}(\sigma').$$
--
--   This is why the rounded instance may be scheduled in place of the original one: each machine was modified to run no faster than its true speed.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 9, §3 ("By ensuring that each machine is modified to run no faster than its true speed …")

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_Rounding

namespace UniformPrecSched.Makespan

/-- §3, p. 9: every feasible schedule of the rounded instance, read on the corresponding original
machines with the same start times, is a feasible schedule of the original instance of no greater
length. -/
theorem rounded_schedule_lift {n m : ℕ} (I : Instance n m) (α β : ℝ) (hα : 1 ≤ α) (hβ : 1 < β)
    (σ' : Schedule (roundInstance I α β hα hβ)) :
    ∃ σ : Schedule I, (∀ j, σ.μ j = keptEmb I α (σ'.μ j) ∧ σ.S j = σ'.S j) ∧
      σ.makespan ≤ σ'.makespan := by sorry

end UniformPrecSched.Makespan
