-- Prove2me | Theorems.Thm_SchedComplexity_TotalCompletion_claim_C
-- name    : SchedComplexity.TotalCompletion.claim_C
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:09:40.753297+00:00
-- url     : https://prove2.me/theorems/083d07d9-6641-4288-8430-65bcea4e56bb
-- title:
--   Theorem 4(a), claim (C): exactly $t$ jobs precede $J_n$
-- statement:
--   Let $a_1,\dots,a_t,b$ be positive integers with $0<b<A$, and consider the instance and threshold $y$ of the construction of Theorem 4(a). In every feasible schedule with $\sum_jC_j\le y$, exactly $t$ jobs start before the last job $J_n$:
--
--   $$\bigl|\{\,j : B_j<B_n\,\}\bigr| = t .$$
--
--   This is claim (C) of the converse direction.
--
--   **Formalization Note** "Precede" is read as "start earlier on the machine". The paper's proof counts the jobs of $T\cup T'$ before $J_n$; by claim (A) no job of $U$ precedes $J_n$, so the count over all jobs is the same.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 22 (statement) and p. 23 (proof), proof of Theorem 4(a), claim (C)

import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

/-- Proof of Theorem 4(a), claim (C) (pp. 22–23): in every feasible schedule of the constructed
instance with `Σ_j C_j ≤ y`, exactly `t` jobs start before the last job `J_n`. -/
theorem claim_C {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    (Finset.univ.filter fun j => B j < B (lastJob a b)).card = t := by sorry

end SchedComplexity.TotalCompletion
