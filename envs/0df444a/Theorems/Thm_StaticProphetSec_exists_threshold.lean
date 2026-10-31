-- Prove2me | Theorems.Thm_StaticProphetSec_exists_threshold
-- name    : StaticProphetSec.exists_threshold
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:04.386772+00:00
-- url     : https://prove2.me/theorems/0ef91852-3926-477e-9863-b32554b3e18b
-- title:
--   Remark 1 — a policy $(t,p)$ with expected utilization $\gamma_k$ exists when $k\le n$
-- statement:
--   For $1\le k\le n$ and every instance $F$ there are $t\ge0$ and $p\in[0,1]$ such that the policy $(t,p)$ has expected utilization exactly $\gamma_k$.
--
--   For continuous distributions a plain threshold suffices; tie-breaking handles discrete distributions.
--
--   Differences from the source:
--
--   - generalization: continuous $F_i$, and "tie-breaking may be required" for discrete $F_i$ → every instance, with a policy $(t,p)$; reason: the same remark says tie-breaking makes utilization adjustable continuously; the continuous case is covered
--   - reading: "from 1 (at $t=0$)" → the hypothesis $k\le n$; reason: expected utilization is at most $n/k$, so the claim fails for $n<k$ ($n=1$, $k=2$: $1/2<\gamma_2$); §1 assumes $n>k$
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Remark 1, p.5

import Mathlib
import Definitions.Def_StaticProphetSec_gamma
import Definitions.Def_StaticProphetSec_expUtil

open MeasureTheory

namespace StaticProphetSec

/-- Existence of the threshold (Arnosti & Ma, arXiv:2108.12893v2, Remark 1, p.5, "it is always
possible to choose a threshold such that expected utilization equals γ_k … tie-breaking may be
required"): for `k ≤ n`, every instance has a policy `(t, p)` with expected utilization `γ_k`. -/
theorem exists_threshold {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, μ i (Set.Iio 0) = 0) :
    ∃ t p : ℝ, 0 ≤ t ∧ 0 ≤ p ∧ p ≤ 1 ∧ expUtil k μ t p = ENNReal.ofReal (gamma k) := by sorry

end StaticProphetSec
