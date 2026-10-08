-- Prove2me | Theorems.Thm_SchedComplexity_NoWait_delay_construction
-- name    : SchedComplexity.NoWait.delay_construction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:14:33.509063+00:00
-- url     : https://prove2.me/theorems/2ebc22e0-0c6e-4701-9194-d1dc0f4f65f3
-- title:
--   Proof of Theorem 5(a) — c_jk = μ + 2λ if (j,k) ∈ A, μ + 2λ + 2 if (j,k) ∉ A
-- statement:
--   Under the hypotheses of the positivity statement (admissible $\iota$, $\lambda\ge1$, $\mu\ge2\lambda+3$), the delays (9) of the instance constructed in Theorem 5 are, for distinct jobs $j\ne k$,
--   $$c_{jk}=\begin{cases}\mu+2\lambda&\text{if }(j,k)\in A,\\ \mu+2\lambda+2&\text{if }(j,k)\notin A.\end{cases}$$
--
--   The paper: "Through the choice of $\lambda$, it is immediate that $q_{ji}-q_{k,i-1}$ is maximal for $i=\iota(j,k)$." Arcs of $G$ thus become cheap transitions between consecutive jobs, non-arcs expensive ones.
--
--   **Formalization Note** The delay is computed for the instance's processing times (the natural-number conversion of the integer processing times).
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 25, proof of Theorem 5(a)

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

/-- p. 25: in the construction of Theorem 5, for an admissible `ι`, `λ ≥ 1`, `μ ≥ 2λ + 3` and
distinct jobs `j ≠ k`, the delay (9) is `c_{jk} = μ + 2λ` if `(j,k) ∈ A` and `μ + 2λ + 2` if
`(j,k) ∉ A`. -/
theorem delay_construction {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu)
    (j k : Fin n) (hjk : j ≠ k) :
    delay (procTimes adj ι lam mu) (numMachines_pos n) j k =
      if adj j k = true then (mu : ℤ) + 2 * lam else (mu : ℤ) + 2 * lam + 2 := by sorry

end SchedComplexity.NoWait
