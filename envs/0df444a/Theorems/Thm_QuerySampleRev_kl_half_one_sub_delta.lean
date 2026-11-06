-- Prove2me | Theorems.Thm_QuerySampleRev_kl_half_one_sub_delta
-- name    : QuerySampleRev.kl_half_one_sub_delta
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:07.506032+00:00
-- url     : https://prove2.me/theorems/15917030-9450-4501-9cdf-7b9d3baf08a4
-- title:
--   Lemma 10 (proof, last step) — $\mathrm{KL}(\tfrac12,1-\delta)=\tfrac12\log\tfrac1{4\delta(1-\delta)}\ge\tfrac1{16}\log\tfrac1\delta$
-- statement:
--   For $0<\delta\le1/4$, the Bernoulli KL divergence between parameters $1/2$ and $1-\delta$ satisfies
--   $$
--   \mathrm{KL}\big(\tfrac12,1-\delta\big)=\frac12\log\frac1{4\delta(1-\delta)}\qquad\text{and}\qquad \mathrm{KL}\big(\tfrac12,1-\delta\big)\ge\frac1{16}\log\frac1\delta .
--   $$
--   Logarithms are natural. This is the last inequality in the proof of Lemma 10, which converts a weighted binary KL bound into the $\tfrac{W}{16}\log\tfrac1\delta$ information requirement.
--
--   **Formalization Note** The binary KL is `ExploreFirst.FundIneq.klBer`, valued in $[0,\infty]$; the real right-hand sides enter through $\mathrm{ofReal}$ (they are nonnegative for $\delta\le1/4$).
--
--   Differences from the source:
--   - encoding: the real-valued identity and inequality $W\,\mathrm{KL}(1/2,1-\delta)\ge (W/16)\log(1/\delta)$ → both stated for $\mathrm{KL}(1/2,1-\delta)$ in $[0,\infty]$ with $\mathrm{ofReal}$ of the real right-hand sides; the factor $W>0$ is cancelled; reason: the right-hand sides are nonnegative for $0<\delta\le1/4$; same content
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), proof of Lemma 10, p.23 (PDF p.25), last sentence

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting

open scoped ENNReal

namespace QuerySampleRev

/-- **The last step of Lemma 10: `KL(1/2, 1 − δ) ≥ (1/16) log(1/δ)`.** Jin, Tang, Wang, Zhang,
*Query-Sample Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), proof of Lemma 10,
p.23 (PDF 25): "The last inequality uses `KL(1/2, 1 − δ) = (1/2) log(1/(4δ(1 − δ)))` and `δ ≤ 1/4`", the
inequality being `W KL(1/2, 1 − δ) ≥ (W/16) log(1/δ)`.

For `0 < δ ≤ 1/4`, the Bernoulli KL divergence `KL(1/2, 1 − δ)` equals `(1/2) log(1/(4δ(1 − δ)))` and is at
least `(1/16) log(1/δ)` (natural logarithms). -/
theorem kl_half_one_sub_delta {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    ExploreFirst.FundIneq.klBer (1 / 2) (1 - δ) =
        ENNReal.ofReal (1 / 2 * Real.log (1 / (4 * δ * (1 - δ)))) ∧
      ENNReal.ofReal (1 / 16 * Real.log (1 / δ)) ≤ ExploreFirst.FundIneq.klBer (1 / 2) (1 - δ) := by sorry

end QuerySampleRev
