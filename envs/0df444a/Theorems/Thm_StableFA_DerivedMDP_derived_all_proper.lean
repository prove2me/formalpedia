-- Prove2me | Theorems.Thm_StableFA_DerivedMDP_derived_all_proper
-- name    : StableFA.DerivedMDP.derived_all_proper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:07.175153+00:00
-- url     : https://prove2.me/theorems/74ed75dd-5c14-4c55-b1b3-f7ba3f1cbd7f
-- title:
--   §4, p. 10 — if A is self-weighted for M and all policies of M are proper, M′ has only proper policies
-- statement:
--   Let $M$ be a finite nondiscounted Markov decision process in which every policy is proper, let $A$ be an averager that is self-weighted for $M$, and let $M'$ be the derived MDP of Theorem 4.1 with $\gamma=1$. Then:
--
--   1. there is an integer $m>0$ such that, for every admissible (possibly nonstationary) policy $\pi$ of $M'$ and every starting state $i$,
--   $$P\{x_m\ne 1\mid x_0=i,\pi\}<1\quad\text{in } M' ;$$
--   2. every stationary policy of $M'$ is proper.
--
--   The report proves this in the paragraph after the definition of self-weighted averagers. Part 1 is exactly the hypothesis of the stochastic shortest path theorem applied to $M'$, which is how the convergence of approximate value iteration follows.
--
--   **Formalization Note** $M'$ is `derivedModel M A 1`. The page states the claim as "$M'$ will have only proper policies"; part 2 is that wording, and part 1 is the uniform bound the page's argument establishes ("no matter what state we start from, we have a positive probability of reaching state 1 in $m-1$ steps"), written as Bertsekas' Assumption 7.2.1, the hypothesis of `BertsekasDP.ssp_main_theorem`. The hypotheses concern $M$ and $A$ only.
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 10, §4, paragraph after the definition of self-weighted

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_DerivedMDP_Setting

namespace StableFA.DerivedMDP

theorem derived_all_proper {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (A : Averager n)
    (hproper : ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper M μ)
    (hself : SelfWeighted M A) :
    (∃ m : ℕ, 0 < m ∧ ∀ π : ℕ → Fin n → C, BertsekasSSPAdmissible (derivedModel M A 1) π →
        ∀ i, BertsekasSSPSurvival (derivedModel M A 1) π m i < 1) ∧
      ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper (derivedModel M A 1) μ := by sorry

end StableFA.DerivedMDP
