-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaJSched_eq_3_10
-- name    : SingleMachineSched.AlphaJSched.eq_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:19:43.36965+00:00
-- url     : https://prove2.me/theorems/bba4ff38-56e1-4491-87f3-874a9f6f9f23
-- title:
--   Eq. (3.10) — $M^{LP}_j=t_j(0^+)+\sum_{k\in N_2}(1-\mu_k)p_k+\tfrac12p_j$
-- statement:
--   Let $n$ jobs have integral processing times $p_j>0$, integral release dates $r_j\ge0$ and weights $w_j>0$, indexed in nonincreasing order of $w_j/p_j$. Fix a job $j$, and let $t_j(0^+)$ be its start time in the LP schedule, $N_2$ the set of jobs processed between the start and the completion of $j$, and $\mu_k$ the fraction of $j$ processed before the start of $k$. Then
--   $$M^{LP}_j=t_j(0^+)+\sum_{k\in N_2}(1-\mu_k)\,p_k+\tfrac12p_j .$$
--
--   This expresses the mean busy time through the structure of the LP schedule around $j$; together with (3.11) it is what the proof of Theorem 3.9 compares.
--
--   **Formalization Note.** $N_2$ and $\mu_k$ are the definitions of the file `LPStructure`. The weights and their order are the paper's standing assumptions; the smallest-index rule is what makes the structure hold.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 182, Section 3.2, Eq. (3.10)

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_LPSchedule
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaPoints
import Definitions.Def_SingleMachineSched_AlphaJSched_LPStructure

namespace SingleMachineSched.AlphaJSched

/-- Equation (3.10): `M^LP_j = t_j(0⁺) + Σ_{k ∈ N₂} (1 − μ_k) p_k + p_j / 2`. -/
theorem eq_3_10 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j) (j : Fin n) :
    mLP p r j =
      startTime (lpSet p r) j + ∑ k ∈ N2 p r j, (1 - mu p r j k) * (p k : ℝ) +
        (p j : ℝ) / 2 := by sorry

end SingleMachineSched.AlphaJSched
