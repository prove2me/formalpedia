-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_poisson_h
-- name    : SampleCRS.AlmostGreedy.poisson_h
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:21.828103+00:00
-- url     : https://prove2.me/theorems/ad80494f-d0e1-4fca-ac65-4d0dee0fdc3d
-- title:
--   §4.1, p.16: the exact Poisson value of h
-- statement:
--   For each integer capacity $k\ge1$, let $Z$ have Poisson distribution of mean $k$. For the defined function $h_k$,
--   $$\mathbb E[h_k(Z)]=1-\Pr[Z=k]=1-e^{-k}\frac{k^k}{k!}=\gamma_k.$$
--
--   Both equalities through the point mass are retained. This identifies the exact constant in Theorem 4.1, using the same Poisson law and acceptance-rate convention as the referenced identities (6).
--
--   Differences from the source:
--   - encoding: the standing assumption k ≥ 1 in §2, p.5 → an explicit hypothesis 1 ≤ k; reason: Lean natural numbers include zero
--   - encoding: expectation under Z ∼ Poi(k) → the published poisE series against poissonMeasure at the nonnegative real k; reason: h takes values in [0,1], so the series converges absolutely and its default value is irrelevant
--   - encoding: the chain E[h(Z)] = 1−Pr[Z=k] = 1−exp(−k)k^k/k! → both equalities as a conjunction, ending in published gamma k; reason: gamma is definitionally the exact exponential-factorial expression
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §4.1, display after eq. (6), p.16

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_experiment
import Definitions.Def_SampleCRS_AlmostGreedy_h
import Definitions.Def_StaticProphetSec_pbE
import Definitions.Def_StaticProphetSec_poisE
import Definitions.Def_StaticProphetSec_gamma

open scoped NNReal

namespace SampleCRS.AlmostGreedy

 /-- Both equalities of the Poisson-value display after (6), p.16. -/
theorem poisson_h (k : ℕ) (hk : 1 ≤ k) :
    StaticProphetSec.poisE (h k) (k : ℝ≥0) =
      1 - (ProbabilityTheory.poissonMeasure (k : ℝ≥0)).real {k} ∧
    1 - (ProbabilityTheory.poissonMeasure (k : ℝ≥0)).real {k} =
      StaticProphetSec.gamma k := by sorry

end SampleCRS.AlmostGreedy
