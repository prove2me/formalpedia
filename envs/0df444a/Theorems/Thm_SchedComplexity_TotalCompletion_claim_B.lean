-- Prove2me | Theorems.Thm_SchedComplexity_TotalCompletion_claim_B
-- name    : SchedComplexity.TotalCompletion.claim_B
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:09:30.600996+00:00
-- url     : https://prove2.me/theorems/80b266f1-33ec-47b0-936c-a24604689840
-- title:
--   Theorem 4(a), claim (B): $B_j\le\sigma$ for some $j\in U$, hence $\sum_{j\notin U}C_j\le u$
-- statement:
--   Let $a_1,\dots,a_t,b$ be positive integers with $0<b<A$, and consider the instance and threshold $y$ of the construction of Theorem 4(a). In every feasible schedule with $\sum_jC_j\le y$:
--
--   1. some job of $U$ starts no later than $\sigma$: $B_j\le\sigma$ for some $j\in U$;
--   2. the jobs outside $U$ satisfy $$\sum_{j\notin U}C_j\le u .$$
--
--   Part 1 is claim (B); part 2 is the consequence the paper draws from (A) and (B) and uses in the proofs of (C) and (D).
--
--   **Formalization Note** Starting times are natural numbers (Section 3); the paper's proof passes from $B_j>\sigma$ to $B_j\ge\sigma+1$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 22 (statement) and p. 23 (proof and consequence), proof of Theorem 4(a), claim (B)

import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

/-- Proof of Theorem 4(a), claim (B) and its consequence (pp. 22–23): in every feasible schedule
of the constructed instance with `Σ_j C_j ≤ y`, some job of `U` starts at a time `B_j ≤ σ`, and
`Σ_{j∉U} C_j ≤ u`. -/
theorem claim_B {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    (∃ j ∈ groupU a b, B j ≤ sigma a b) ∧
      ∑ j ∈ (groupU a b)ᶜ, completion (procTime a b) B j ≤ uCount a b := by sorry

end SchedComplexity.TotalCompletion
