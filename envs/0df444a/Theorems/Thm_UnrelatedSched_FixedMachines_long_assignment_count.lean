-- Prove2me | Theorems.Thm_UnrelatedSched_FixedMachines_long_assignment_count
-- name    : UnrelatedSched.FixedMachines.long_assignment_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:55.659861+00:00
-- url     : https://prove2.me/theorems/e995638f-3343-48d7-846c-d24c536b0dbe
-- title:
--   §3, p. 6 — fewer than $(n+1)^{m/\varepsilon}$ schedules of long assignments
-- statement:
--   Let $P=(p_{ij})$ be an $m\times n$ matrix of positive integer processing times with $m\ge 1$ machines and $n\ge 1$ jobs, let $d\ge 0$ be an integer deadline and $\varepsilon>0$. Call an assignment of job $j$ to machine $i$ long if $p_{ij}>\varepsilon d$, and call a partial schedule of long assignments admissible if the long assignments to each machine take at most $d$ time in total. Then
--
--   1. in every admissible schedule of long assignments, every machine carries fewer than $1/\varepsilon$ long assignments; and
--   2. the number of admissible schedules of long assignments satisfies
--
--   $$
--   \#\{L : L \text{ admissible}\} < (n+1)^{m/\varepsilon}.
--   $$
--
--   The paper's words: "No machine can handle $1/\varepsilon$ or more long assignments before time $d$. Thus, for any instance there are less than $(n+1)^{m/\varepsilon}$ schedules of long assignments." The count is what bounds the number of linear programs the procedure $A_\varepsilon$ solves, and hence its running time for fixed $m$ and $\varepsilon$.
--
--   **Formalization Note** The exponent $m/\varepsilon$ is a real number and the power is the real power `Real.rpow`; it is not rounded. The hypotheses $n\ge 1$ and $m\ge 1$ are needed for the strict inequality: for $n=0$ there is exactly one (empty) schedule and $(0+1)^{m/\varepsilon}=1$. The count is `Set.ncard` of a subset of a finite type, so it is the honest cardinality.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 6, Section 3, proof of Theorem 3

import Mathlib
import Definitions.Def_UnrelatedSched_FixedMachines_LongAssignment

namespace UnrelatedSched.FixedMachines

/-- §3, p. 6: in an admissible schedule of long assignments for `(P, d)` no machine carries
`1/ε` or more long assignments, and (for `n ≥ 1`, `m ≥ 1`) there are fewer than
`(n + 1)^{m/ε}` admissible schedules of long assignments. -/
theorem long_assignment_count {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε) (d : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (∀ L, IsAdmissible P ε d L →
      ∀ i, ((Finset.univ.filter (fun j => L j = some i)).card : ℝ) < 1 / ε) ∧
    (({L : Fin n → Option (Fin m) | IsAdmissible P ε d L}.ncard : ℕ) : ℝ) <
      ((n : ℝ) + 1) ^ ((m : ℝ) / ε) := by sorry

end UnrelatedSched.FixedMachines
