-- Prove2me | Theorems.Thm_SchedComplexity_TotalCompletion_claim_A
-- name    : SchedComplexity.TotalCompletion.claim_A
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:09:22.112991+00:00
-- url     : https://prove2.me/theorems/c37a6c9c-e19e-407f-8a00-4e0c58e6383e
-- title:
--   Theorem 4(a), claim (A): $\{J_j\mid j\notin U\}$ precedes $\{J_j\mid j\in U\}$
-- statement:
--   Let $a_1,\dots,a_t,b$ be positive integers with $0<b<A$, and consider the instance and threshold $y$ of the construction of Theorem 4(a). In every feasible schedule with $\sum_jC_j\le y$, every job outside $U$ is processed before every job of $U$:
--
--   $$B_{j'}<B_j\qquad\text{for all } j'\notin U,\ j\in U .$$
--
--   This is claim (A) of the converse direction: the long jobs of $U$ come last.
--
--   **Formalization Note** "Precedes" is read as "is processed earlier on the machine", i.e. starts earlier; there are no precedence constraints in this problem. Starting times are natural numbers (Section 3).
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 22 (statement) and p. 23 (proof), proof of Theorem 4(a), claim (A)

import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

/-- Proof of Theorem 4(a), claim (A) (pp. 22–23): in every feasible schedule of the constructed
instance with `Σ_j C_j ≤ y`, every job outside `U` is processed before every job of `U`
(`{J_j | j ∉ U}` precedes `{J_j | j ∈ U}`), i.e. starts earlier. -/
theorem claim_A {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    ∀ j' j : Fin (numJobs a b), j' ∉ groupU a b → j ∈ groupU a b → B j' < B j := by sorry

end SchedComplexity.TotalCompletion
