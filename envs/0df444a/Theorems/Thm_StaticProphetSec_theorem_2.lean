-- Prove2me | Theorems.Thm_StaticProphetSec_theorem_2
-- name    : StaticProphetSec.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:34.200843+00:00
-- url     : https://prove2.me/theorems/0b49b781-9b03-43ee-84f0-2cc09e9a54d1
-- title:
--   Theorem 2 — expected utilization $\gamma_k$ earns at least $\gamma_k$ times the LP value and the prophet's value (corrected: \"equal to $\gamma_k$\", not \"equal to $k$\")
-- statement:
--   Let $k\ge1$, let $V_1,\dots,V_n$ be independent non-negative values with arbitrary laws $F_1,\dots,F_n$, arriving in a uniformly random order. For every static threshold policy $(t,p)$ whose expected utilization is $\gamma_k=1-e^{-k}k^k/k!$,
--
--   $$\mathcal{PHT}_k(F)\le\mathcal{LP}_k(F)\qquad\text{and}\qquad\gamma_k\,\mathcal{LP}_k(F)\le\mathcal{ST}^t_k(F).$$
--
--   So the performance of the policy is at least $\gamma_k$ times the prophet's value, and at least $\gamma_k$ times the stronger LP benchmark. Moreover, if $k\le n$, such a policy $(t,p)$ exists.
--
--   This is the paper's main result: the first $k$-unit guarantee of $\gamma_k$ for a static threshold in the prophet secretary problem.
--
--   Differences from the source:
--
--   - correction: "expected utilization is equal to $k$" → expected utilization is equal to $\gamma_k$; reason: the printed statement is false: $k=1$, $n=2$, $V_1\equiv1$, $V_2\equiv10$, $t=0$ has utilization $1=k$ and performance $11/2<10\gamma_1$ (machine-checked in the mission's sanity file); the sentence before the theorem says $\gamma_k$
--   - generalization: threshold $t$ and $D^t(V)$ → policy $(t,p)$ with tie-breaking coins and $D$ counting eligible applicants; reason: Remark 1, p.5, says all results apply to it; $p=0$ recovers the plain threshold
--   - generalization: at least $\gamma_k$ times the prophet's value → $\mathcal{PHT}\le\mathcal{LP}$ and $\gamma_k\mathcal{LP}\le\mathcal{ST}$; reason: p.5: "our proof establishes that the statement remains true if the prophet's value is replaced by" the LP relaxation; the two inequalities imply the printed conclusion
--   - generalization: values with finite expectations are the implicit reading of ratios → expectations in $[0,\infty]$ with no integrability assumption; reason: the source assumes none; every finite instance is covered
--   - generalization: $n>k$ applicants (p.2) → the guarantee for every $n$; reason: §3 does not use it; the proof's padding step handles small $n$
--   - generalization: a statement about any threshold with the given utilization → an added clause: such a policy exists when $k\le n$; reason: p.3, "there always exists", and Remark 1; it keeps the guarantee from being vacuous and is false for $n<k$
--   - encoding: ratio "at least $\gamma_k$ times" → the product inequality $\gamma_k\mathcal{LP}\le\mathcal{ST}$; reason: no division by a possibly zero benchmark
--   - encoding: $x_i\ge0$ in $\mathcal{LP}_k$ → $0\le x_i\le1$; reason: $F_i^{-1}$ is undefined below $0$ and $x_i$ is a probability, p.16; only undefined cases are excluded
--   - encoding: random arrival order and tie-break flips → a uniform permutation of $n$ positions and coins drawn in advance; reason: same law; each coin is read at most once
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Theorem 2, p.5 (proof §3.3, p.18); Remark 1, p.5

import Mathlib
import Definitions.Def_StaticProphetSec_gamma
import Definitions.Def_StaticProphetSec_performance
import Definitions.Def_StaticProphetSec_expUtil
import Definitions.Def_StaticProphetSec_prophet
import Definitions.Def_StaticProphetSec_lpValue

open MeasureTheory

namespace StaticProphetSec

/-- Theorem 2 (Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet
Secretary Problem, arXiv:2108.12893v2, Theorem 2, p.5), corrected, at the strength the paper
claims. For every instance `(k, F)` and every policy `(t, p)` whose expected utilization equals
`γ_k`: the prophet's value is at most the LP value, and the policy's performance is at least
`γ_k` times the LP value, hence at least `γ_k` times the prophet's value. If `k ≤ n` such a policy
exists.

**Formalization Note.** The page prints "expected utilization is equal to k"; this is a typo for
`γ_k` ("setting the threshold so that expected utilization equals γ_k", the sentence before the
theorem). Tie-breaking is Remark 1 ("All of our results apply to any static threshold policy with
tie-breaking"; `p = 0` is a plain threshold), the LP benchmark is the paragraph after Remark 1,
and the ratio is written as a product. Everything lies in `ℝ≥0∞`, so no integrability is
assumed. -/
theorem theorem_2 {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, μ i (Set.Iio 0) = 0) :
    (∀ t p : ℝ, 0 ≤ t → 0 ≤ p → p ≤ 1 → expUtil k μ t p = ENNReal.ofReal (gamma k) →
      prophet k μ ≤ lpValue k μ ∧
      ENNReal.ofReal (gamma k) * lpValue k μ ≤ performance k μ t p) ∧
    (k ≤ n →
      ∃ t p : ℝ, 0 ≤ t ∧ 0 ≤ p ∧ p ≤ 1 ∧ expUtil k μ t p = ENNReal.ofReal (gamma k)) := by sorry

end StaticProphetSec
