-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_lp_lower_bound
-- name    : UniformPrecSched.Makespan.lp_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:31:10.766719+00:00
-- url     : https://prove2.me/theorems/ee159a52-7f14-42c8-b81c-d3dff03ef4d2
-- title:
--   §3, p. 6 — LP has an optimal solution, and its value D̄ is a lower bound on C*_max
-- statement:
--   Let $I$ be an instance of $Q|prec|C_{\max}$. The linear program LP (minimize $D$ subject to (1)–(5) and (8)) has an optimal solution $(\bar x, \bar C, \bar D)$, and for every optimal solution and every feasible schedule $\sigma$ of $I$,
--   $$\bar D \le C_{\max}(\sigma).$$
--   In particular $\bar D \le C^*_{\max}$, the length of an optimal schedule.
--
--   This is the lower bound against which the paper's approximation guarantees are proved.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 6, paragraph after (8) (LP and its optimal value D̄ ≤ C*max)

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP

namespace UniformPrecSched.Makespan

/-- §3, p. 6: `LP` has an optimal solution, and its optimal value `D̄` is a lower bound on the
length of every feasible schedule (hence on the optimal schedule length `C*_max`). -/
theorem lp_lower_bound {n m : ℕ} (I : Instance n m) :
    (∃ x C D, LPOptimal I x C D) ∧
      ∀ x C D, LPOptimal I x C D → ∀ σ : Schedule I, D ≤ σ.makespan := by sorry

end UniformPrecSched.Makespan
