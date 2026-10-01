-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaSched_eq_3_10
-- name    : SingleMachineSched.AlphaSched.eq_3_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:13:13.882097+00:00
-- url     : https://prove2.me/theorems/db9dadff-472b-4301-b1d5-3cb6b661d6c3
-- title:
--   Eq. (3.10) — $M^{LP}_j = t_j(0^+) + \sum_{k\in N_2}(1-\mu_k)p_k + \tfrac12 p_j$
-- statement:
--   Let $n$ jobs have integral processing times $p_j > 0$, integral release dates $r_j \ge 0$ and weights $w_j > 0$, indexed by nonincreasing $w_j/p_j$. Fix a job $j$. Let $t_j(0^+)$ be its start time in the LP schedule, $N_2$ the set of jobs $k \ne j$ processed in the LP schedule between the start and the completion of $j$, and, for $k \in N_2$, $\mu_k$ the fraction of job $j$ processed before the start of job $k$. Then
--
--   $$M^{LP}_j = t_j(0^+) + \sum_{k \in N_2} (1 - \mu_k)\, p_k + \frac12 p_j .$$
--
--   The identity expresses the LP mean busy time through the structure of the LP schedule around job $j$; it is the form in which the paper compares the expected completion time with $M^{LP}_j + \tfrac12 p_j$.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 182, Eq. (3.10)

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaSched_AlphaPoints

namespace SingleMachineSched.AlphaSched

/-- Eq. (3.10) (Goemans et al. 2002, p. 182): in the LP schedule,
`M^LP_j = t_j(0⁺) + Σ_{k ∈ N₂} (1 - μ_k) p_k + p_j / 2`. -/
theorem eq_3_10 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j) (j : Fin n) :
    mLP p r j = startTime (lpSet p r) j +
      ∑ k ∈ N2 p r j, (1 - mu p r j k) * (p k : ℝ) + (p j : ℝ) / 2 := by sorry

end SingleMachineSched.AlphaSched
