-- Prove2me | Theorems.Thm_UnrelatedSched_ThreeHalves_dummy_count
-- name    : UnrelatedSched.ThreeHalves.dummy_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:36:09.416952+00:00
-- url     : https://prove2.me/theorems/5cbc01cd-3b6e-4042-9db7-61f5d98ee4dd
-- title:
--   Theorem 5, proof (p. 7) — the total number of dummy jobs is m − n
-- statement:
--   Let $T_1,\dots,T_m$ be an instance of 3-dimensional matching over sets of size $n$, and let $t_j$ be the number of triples containing $a_j$. Suppose every $a_j$ lies in at least one triple, $t_j \ge 1$ for all $j$. Then the number of dummy jobs of the instance of Theorem 5 is $m - n$:
--   $$\sum_{j=1}^{n} (t_j - 1) + n = m.$$
--
--   The paper notes this in passing ("the total number of dummy jobs is $m - n$, as before"); it is the count that leaves exactly one machine per type free for element jobs.
--
--   **Formalization Note** The identity is stated as $\sum_j (t_j - 1) + n = m$ to avoid subtracting $n$ from $m$ in the natural numbers; under $t_j \ge 1$ the subtraction $t_j - 1$ is exact.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 7, Section 4, proof of Theorem 5

import Mathlib
import Definitions.Def_UnrelatedSched_ThreeHalves_Theorem5Instance

namespace UnrelatedSched.ThreeHalves

/-- Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §4, proof of Theorem 5, p. 7: when every
`a_j` lies in at least one triple (`t_j ≥ 1`), the total number `Σ_j (t_j − 1)` of dummy jobs is
`m − n`, stated without subtraction as `Σ_j (t_j − 1) + n = m`. -/
theorem dummy_count {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (hT : ∀ j : Fin n, 1 ≤ typeCount T j) :
    (∑ j : Fin n, (typeCount T j - 1)) + n = m := by sorry

end UnrelatedSched.ThreeHalves
