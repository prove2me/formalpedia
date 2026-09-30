-- Prove2me | Theorems.Thm_SingleMachineSched_LPRelax_eq_2_6
-- name    : SingleMachineSched.LPRelax.eq_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T04:20:41.141689+00:00
-- url     : https://prove2.me/theorems/e8e34e62-d844-4220-b2cc-7fc577f8b61d
-- title:
--   Eq. (2.6) — $M^{LP}_j$ through the slot vector $y^{LP}$
-- statement:
--   Let $n$ jobs have integral processing times $p_j > 0$ and integral release dates $r_j \ge 0$, and let the horizon $T \in \mathbb N$ bound the makespan of some feasible nonpreemptive schedule. For every job $j$, the mean busy time of $j$ in the LP schedule is
--
--   $$M^{LP}_j = \frac{1}{p_j} \sum_{\tau = r_j}^{T-1} y^{LP}_{j\tau}\Big(\tau + \frac12\Big), \tag{2.6}$$
--
--   where $y^{LP}_{j\tau} = 1$ if the LP schedule processes $j$ in $[\tau, \tau+1)$ and $0$ otherwise.
--
--   Combined with (2.1), this says that the objective of (D) at $y^{LP}$ equals the objective of (R) at $M^{LP}$, which links Theorems 2.2 and 2.5 into Corollary 2.6.
--
--   **Formalization Note** The identity does not depend on how the jobs are indexed, so no sortedness hypothesis appears. The horizon hypothesis ensures that the LP schedule does not process $j$ at or after $T$.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 173, proof of Corollary 2.6, Eq. (2.6)

import Mathlib
import Definitions.Def_SingleMachineSched_LPRelax_LPSchedule
import Definitions.Def_SingleMachineSched_LPRelax_RelaxationD

namespace SingleMachineSched.LPRelax

/-- Equation (2.6): the mean busy time of a job in the LP schedule is
`M^LP_j = (1/p_j) Σ_{τ=r_j}^{T-1} y^LP_{jτ} (τ + 1/2)`. -/
theorem eq_2_6 {n : ℕ} (p r : Fin n → ℕ) (T : ℕ)
    (hp : ∀ j, 0 < p j) (hT : IsMakespanBound p r T) (j : Fin n) :
    mLP p r j = (1 / (p j : ℝ)) * ∑ τ ∈ Finset.Ico (r j) T, yLP p r j τ * ((τ : ℝ) + 1 / 2) := by sorry

end SingleMachineSched.LPRelax
