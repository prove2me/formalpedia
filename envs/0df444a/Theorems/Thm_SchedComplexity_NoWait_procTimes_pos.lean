-- Prove2me | Theorems.Thm_SchedComplexity_NoWait_procTimes_pos
-- name    : SchedComplexity.NoWait.procTimes_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:14:36.782508+00:00
-- url     : https://prove2.me/theorems/3b1afffd-0233-4f08-bdbb-656818f6ea5f
-- title:
--   Proof of Theorem 5(a) — the processing times p_ℓi are strictly positive integers
-- statement:
--   Let $G=(V,A)$ be a directed graph on $n$ vertices, $m=n(n-1)+2$, $\iota$ an admissible assignment of the ordered pairs of distinct jobs to the machines $2,\dots,m-1$, and let $\lambda,\mu$ be integers with
--   $$\lambda\ge1,\qquad \mu\ge2\lambda+3.$$
--   Then every processing time of the construction of Theorem 5, $p_{\ell1}=q_{\ell1}$ and $p_{\ell i}=q_{\ell i}-q_{\ell,i-1}$ ($i=2,\dots,m$), satisfies
--   $$p_{\ell i}\ge1.$$
--
--   The paper: "Through the choice of $\mu$, these processing times are all strictly positive integers." This makes the construction a valid instance and supplies the positivity hypothesis of the travelling-salesman reformulation.
--
--   **Formalization Note** The processing times are computed in $\mathbb Z$; this statement is what justifies their conversion to natural numbers in the instance.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), pp. 24–25, proof of Theorem 5(a)

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

/-- p. 25: "Through the choice of μ, these processing times are all strictly positive integers":
for an admissible `ι`, `λ ≥ 1` and `μ ≥ 2λ + 3`, every processing time `p_{ℓ i}` of the
construction is at least `1`. -/
theorem procTimes_pos {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu)
    (ℓ : Fin n) (r : Fin (numMachines n)) :
    1 ≤ procTimeInt adj ι lam mu ℓ r := by sorry

end SchedComplexity.NoWait
