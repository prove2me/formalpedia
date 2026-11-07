-- Prove2me | Theorems.Thm_StatUnlearn_tof_le_tof_comp
-- name    : StatUnlearn.tof_le_tof_comp
-- status  : Proved
-- author  : @2017Advanced@
-- created : 2026-11-06T20:17:29.576288+00:00
-- url     : https://prove2.me/theorems/cc7c4ec3-2a53-41cf-99e5-fd1a93bfa8bb
-- title:
--   Data-processing inequality for the trade-off function
-- statement:
--   Let $\kappa$ be a Markov kernel from a measurable space $W$ to a measurable space $V$, let $P,Q$ be probability distributions on $W$, and let $\kappa_*P$, $\kappa_*Q$ be their images under $\kappa$. Then for every type-I level $t\ge0$,
--   $$T(P,Q)(t)\ \le\ T(\kappa_*P,\ \kappa_*Q)(t).$$
--   Post-processing cannot make two distributions easier to tell apart: a test $\varphi$ on the output space pulls back to the test $w\mapsto\int\varphi\,d\kappa(w)$ on the input space, with exactly the same type-I and type-II errors, so every error pair achievable for the post-processed distributions is already achievable for the originals and the infimum over the larger set is no larger.
--
--   This is the data-processing inequality for trade-off functions, the direction of Blackwell's theorem that governs every information-theoretic statement in the paper: it converts "$\kappa$ maps one experiment to another" into an inequality between trade-off functions, and it is what makes the Gaussian baselines comparable in Proposition 3.1 and Proposition 2.1.
-- source:
--   Pandey, Kulkarni, "Statistical Unlearning of Distributions: A Hypothesis Testing Approach", arXiv:2605.16645, Theorem A.4 (`thm:Blackwell`), data-processing direction; used in `proof:CoD` and `proof:FRP`

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_su_tof
open MeasureTheory ProbabilityTheory

namespace StatUnlearn

theorem tof_le_tof_comp {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]
    (κ : Kernel W V) [IsMarkovKernel κ] (P Q : Measure W) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (t : ℝ) (ht : 0 ≤ t) :
    tof P Q t ≤ tof (κ ∘ₘ P) (κ ∘ₘ Q) t := by
  sorry

end StatUnlearn
