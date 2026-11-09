-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_theorem_1_2
-- name    : SFMQueryLower.EmptyMin.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:15.597087+00:00
-- url     : https://prove2.me/theorems/adc6a4b1-a07e-477d-b64f-10c522060e52
-- title:
--   Theorem 1.2 — randomized EmptyMin needs n log n expected queries
-- statement:
--   There are absolute constants $c>0$ and $N\ge2$ such that for every integer $n\ge N$,
--   $$R_{1/3}(\operatorname{EmptyMin}_n)\ge c n\log n.$$
--   In operational form, for every randomized causal algorithm $A$ correct with error at most $1/3$ on every real-valued submodular input, there is a fixed submodular $f:2^{[n]}\to\mathbb R$ such that
--   $$\mathbb E_A Q(A,f)\ge c n\log n.$$
--   The same constants work for all sizes, seed spaces and algorithms. The hard input may depend on the algorithm, but is fixed independently of its sampled seed. The complexity is the infimum of worst-case expected query counts from Definition 1.1; the statement includes that bound directly as well as the fixed-input assertion from its proof.
--
--   **Formalization Note** All finite $n$ above the threshold are covered, including nonsquare sizes. Inputs have unrestricted real values; there is no sign, normalization, monotonicity, range or uniqueness promise. Costs may be infinite. The constants remain existential; the conservative numerical witnesses discussed in the brief are not adopted.
--
--   Differences from the source:
--   - encoding: finite labeled ground sets and their subsets → Fin n and Finset (Fin n); reason: bijections relabel every finite source instance
--   - encoding: internal randomized oracle interaction and expected queries → an arbitrary probability seed chooses a causal history strategy; costs are nonnegative extended series; reason: includes general measurable randomness and stopping, preserves infinite cost, and requires only observable-event measurability
--   - encoding: R_{1/3}(EmptyMin_n)=Omega(n log n) and its fixed-input interpretation in the proof → uniform c>0,N>=2 before n and A, with both the infimum lower bound and an actual fixed-input witness; reason: equivalent asymptotic formulations after decreasing a positive constant if necessary; no supremum or infimum attainment is assumed
--   - generalization: ordinary solving algorithms return answers almost surely → nonreturning runs are also allowed and counted as failures; reason: all almost surely halting source algorithms are included; the same indistinguishability and issue-count bounds apply to unsuccessful nonreturning runs
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Theorem 1.2, printed p. 2 / PDF p. 3; restatement and complete proof with arbitrary-size padding, printed p. 10 / PDF p. 11

import Definitions.Def_SFMQueryLower_EmptyMin_EmptyMinProblem

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

/-- Fox, Theorem 1.2, printed p.2 / PDF p.3; proof printed p.10 / PDF p.11.
Both Definition 1.1's complexity lower bound and its fixed-input operational form are stated.
The constants are uniform over every large finite size and every general randomized strategy.
There is no finite-expectation, bounded-depth, finite-seed, or input-range restriction. -/
theorem theorem_1_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        ENNReal.ofReal (c * (n : ℝ) * Real.log (n : ℝ)) ≤ randomizedComplexity n (1 / 3) ∧
        ∀ A : EmptyMinAlgorithm n, SolvesEmptyMin A (1 / 3) →
          ∃ f : Finset (Fin n) → ℝ, NonmonotoneSubmod.Shared.Submodular f ∧
            ENNReal.ofReal (c * (n : ℝ) * Real.log (n : ℝ)) ≤ expectedQueries A f := by sorry

end SFMQueryLower.EmptyMin
