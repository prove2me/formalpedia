-- Prove2me | Theorems.Thm_WhittEfficiency_IS_sec_2_5_class_counts
-- name    : WhittEfficiency.IS.sec_2_5_class_counts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:21.989928+00:00
-- url     : https://prove2.me/theorems/b07c2b78-ecbf-489c-94a3-3539c8d0e130
-- title:
--   §2.5, p. 713 — for t > max dᵢ, N(t) is a sum of independent Poisson(λpᵢdᵢ) class counts
-- statement:
--   In the infinite-server model with Poisson arrivals of rate $\lambda > 0$ and i.i.d. service times, independent of the arrivals, equal to $d_i \ge 0$ with probability $p_i$ ($i = 1,\dots,m$), let $N_i(t)$ be the number of busy servers occupied by class-$i$ customers at time $t$ and $N(t)$ the total number of busy servers. If $t > \max_i d_i$, then
--
--   1. $N_1(t), \dots, N_m(t)$ are mutually independent;
--   2. $N_i(t)$ is Poisson with mean $\lambda p_i d_i$:
--   $$P\big(N_i(t) = k\big) = e^{-\lambda p_i d_i}\,\frac{(\lambda p_i d_i)^k}{k!}, \qquad k = 0, 1, 2, \dots;$$
--   3. almost surely $N(t) = N_1(t) + \cdots + N_m(t)$.
--
--   So the number of busy servers has the distribution of a sum of $m$ independent Poisson variables with means $\lambda p_i d_i$.
--
--   **Formalization Note** Part 3 holds almost surely rather than for every outcome because the counts are `Set.ncard`, which returns $0$ on the null event of infinitely many arrivals in a bounded window. Classes are indexed by `Fin m`.
-- source:
--   Whitt, Understanding the efficiency of multi-server service systems, Management Sci. 38 (1992), p. 713, §2.5, fifth sentence ("Hence, for t > max …")

import Mathlib
import Definitions.Def_WhittEfficiency_IS_Model

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

namespace WhittEfficiency.IS

/-- Whitt 1992, §2.5, p. 713 (the "Hence" sentence): for `t > max d i`, the number of busy
servers is almost surely the sum over classes of the class busy counts, which are independent
Poisson variables with means `lam * p i * d i`. -/
theorem sec_2_5_class_counts {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    {m : ℕ} (p d : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i) (J : ℕ → Ω → Fin m)
    (hM : IsMarkedPoisson μ lam T p J)
    (t : ℝ) (ht : ∀ i, d i < t) :
    iIndepFun (fun i ω => classBusyCount T J d i t ω) μ ∧
    (∀ (i : Fin m) (k : ℕ), μ.real {ω | classBusyCount T J d i t ω = k} =
      Real.exp (-(lam * p i * d i)) * (lam * p i * d i) ^ k / k.factorial) ∧
    ∀ᵐ ω ∂μ, busyCount T (fun j ω => d (J j ω)) t ω = ∑ i, classBusyCount T J d i t ω := by sorry

end WhittEfficiency.IS
