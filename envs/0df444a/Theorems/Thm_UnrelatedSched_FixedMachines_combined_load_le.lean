-- Prove2me | Theorems.Thm_UnrelatedSched_FixedMachines_combined_load_le
-- name    : UnrelatedSched.FixedMachines.combined_load_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:18.797223+00:00
-- url     : https://prove2.me/theorems/a9a938f1-f320-4dea-9e59-ea21acfb87a4
-- title:
--   §3, p. 6 — long plus short assignments use at most $(1+\varepsilon)d$ on each machine
-- statement:
--   Let $P=(p_{ij})$ be an $m\times n$ matrix of positive integer processing times, $d\ge 0$ an integer and $\varepsilon>0$. Let $L$ be a partial schedule of long assignments, with long load $t_i$ on machine $i$, and let $\sigma$ be a schedule that agrees with $L$ on every job $L$ assigns. Suppose that for every machine $i$ the jobs left unassigned by $L$ that $\sigma$ puts on $i$ take total time at most $d-t_i+\varepsilon d$. Then for every machine $i$
--
--   $$
--   \mathrm{load}_i(\sigma) \le t_i + d - t_i + \varepsilon d = (1+\varepsilon)\,d .
--   $$
--
--   This is the step of the proof of Theorem 3 that combines the rounded schedule of short assignments with the schedule of long assignments.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 6, Section 3, proof of Theorem 3

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_FixedMachines_LongAssignment

namespace UnrelatedSched.FixedMachines

open MatousekLP.Scheduling

/-- §3, p. 6: if the schedule `σ` agrees with the schedule of long assignments `L` on the long
jobs and the short assignments take at most `d - t_i + ε d` on every machine `i`, then every
machine `i` is busy for at most `t_i + d - t_i + ε d = (1 + ε) d`. -/
theorem combined_load_le {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε) (d : ℕ) (L : Fin n → Option (Fin m))
    (σ : Fin n → Fin m) (hfollow : ∀ j i, L j = some i → σ j = i)
    (hshort : ∀ i, shortLoad P L σ i ≤ (d : ℝ) - longLoad P L i + ε * (d : ℝ)) :
    ∀ i, load (fun i j => (P i j : ℝ)) σ i ≤ (1 + ε) * (d : ℝ) := by sorry

end UnrelatedSched.FixedMachines
