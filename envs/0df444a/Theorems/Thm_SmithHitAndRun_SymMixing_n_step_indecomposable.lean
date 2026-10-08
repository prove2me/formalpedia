-- Prove2me | Theorems.Thm_SmithHitAndRun_SymMixing_n_step_indecomposable
-- name    : SmithHitAndRun.SymMixing.n_step_indecomposable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:13:14.634758+00:00
-- url     : https://prove2.me/theorems/758e38a6-b707-4a95-853c-2f50afb2c383
-- title:
--   Proof of Theorem 2, step (ii) — indecomposable n-step transitions
-- statement:
--   In the setting of Assumptions (a) and (b), let $P^n(x,A)$ denote the $n$-step transition probability. For every integer $n\ge 2$, there are no disjoint nonempty measurable sets $A_1,A_2$ that are both closed under $P^n$:
--   $$
--   \forall n\ge2,\quad \nexists A_1,A_2\subseteq S:\ A_1\cap A_2=\varnothing\ \text{and }P^n(x,A_j)=1\text{ for all }x\in A_j\ (j=1,2).
--   $$
--   This is the paper's nonperiodicity condition used in Theorem 2. **Formalization Note** $P^n$ is the published `MarkovChainCLT.iterKernel`; it starts with $P^0$ equal to the identity kernel.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1301, Proof of Theorem 2, condition (ii)

import Mathlib.Probability.Kernel.Invariance
import Definitions.Def_MarkovIterKernel
import Definitions.Def_SmithHitAndRun_SymMixing_IsSymmetricMixingKernel
import Definitions.Def_SmithHitAndRun_SymMixing_IsClosedSet

open MeasureTheory ProbabilityTheory

namespace SmithHitAndRun.SymMixing

/-- Smith (1984), proof of Theorem 2, step (ii), p. 1301: every n-step chain,
for n at least two, is indecomposable. -/
theorem n_step_indecomposable {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x) :
    ∀ n : ℕ, 2 ≤ n →
      ¬ ∃ A₁ A₂ : Set α,
        IsClosedSet (MarkovChainCLT.iterKernel P n) A₁ ∧
        IsClosedSet (MarkovChainCLT.iterKernel P n) A₂ ∧ A₁ ∩ A₂ = ∅ := by sorry

end SmithHitAndRun.SymMixing
