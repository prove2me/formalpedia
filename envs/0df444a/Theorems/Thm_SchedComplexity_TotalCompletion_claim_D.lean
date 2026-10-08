-- Prove2me | Theorems.Thm_SchedComplexity_TotalCompletion_claim_D
-- name    : SchedComplexity.TotalCompletion.claim_D
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:10:01.732185+00:00
-- url     : https://prove2.me/theorems/6ed95647-ae06-43a2-9f27-be20ae72fbe2
-- title:
--   Theorem 4(a), claim (D): $B_n=t\tau+b$
-- statement:
--   Let $a_1,\dots,a_t,b$ be positive integers with $0<b<A$, and consider the instance and threshold $y$ of the construction of Theorem 4(a). In every feasible schedule with $\sum_jC_j\le y$, the last job starts exactly at its release date:
--
--   $$B_n=t\tau+b .$$
--
--   This is claim (D) of the converse direction. Together with (C) it shows that exactly $t$ jobs of $T\cup T'$ fill the period $[0,t\tau+b)$.
--
--   **Formalization Note** The claim is about schedules with integral starting times, as in Section 3 of the paper; the printed proof passes from $B_n>t\tau+b$ to $C_n\ge t\tau+b+2$. With real starting times the claim would fail: when KNAPSACK has a solution, $J_n$ can be delayed by a small amount without exceeding $y$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 22 (statement) and p. 23 (proof), proof of Theorem 4(a), claim (D)

import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

/-- Proof of Theorem 4(a), claim (D) (pp. 22–23): in every feasible schedule (integral starting
times) of the constructed instance with `Σ_j C_j ≤ y`, the last job starts exactly at its
release date: `B_n = tτ + b`. -/
theorem claim_D {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    B (lastJob a b) = t * tau a b + b := by sorry

end SchedComplexity.TotalCompletion
