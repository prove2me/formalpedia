-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_theorem_3_1
-- name    : UnbiasedTimeAvg.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:22.629796+00:00
-- url     : https://prove2.me/theorems/a056e347-e61a-4e9e-a604-8bc0ac46f628
-- title:
--   Theorem 3.1 (Rhee and Glynn 2015) — the single term estimator is unbiased
-- statement:
--   Let $(Y_l)_{l\ge0}$ be square-integrable random variables such that $\mathbb E(Y_l)\to\mu_Y$ as $l\to\infty$. Let $(p_l)_{l\ge0}$ be a probability distribution with $p_l>0$ for all $l$, and let $N$ be an $\mathbb N$-valued random variable independent of $(Y_l)_{l\ge0}$ with $\Pr(N=l)=p_l$. Set $Y_{-1}:=0$ and
--   $$Z:=\frac{Y_N-Y_{N-1}}{p_N}.$$
--   If $\sum_{l=0}^\infty\mathbb E\big[(Y_l-Y_{l-1})^2\big]/p_l$ is finite, then $Z$ is square-integrable, $\mathbb E(Z)=\mu_Y$, and
--   $$\mathbb E(Z^2)=\sum_{l=0}^\infty\frac{\mathbb E\big[(Y_l-Y_{l-1})^2\big]}{p_l}.$$
--
--   This randomized-multilevel identity is what turns the biased level estimators into an unbiased correction.
--
--   Differences from the source:
--   - encoding: Σ_l E((Y_l − Y_{l−1})²)/p_l is finite → `Summable` of the real terms; reason: the terms are nonnegative, so summability is finiteness of the sum
--   - encoding: N independent of (Y_l, l ≥ 0) → `IndepFun N (fun ω l => Y l ω) P` for the product σ-algebra on ℕ → ℝ; reason: independence from the whole sequence, as stated
--   - encoding: (p_l, l ≥ 0) a probability distribution with p_l > 0, and Pr(N = l) = p_l → `∀ l, 0 < p l` and `P {N = l} = ofReal (p l)`, with no separate hypothesis `Σ p_l = 1`; reason: the law of N already forces Σ p_l = Σ Pr(N = l) = 1, so a separate hypothesis would be redundant; same instances
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), §3.1 and Theorem 3.1, p.7

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_increment

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UnbiasedTimeAvg

/-- **Theorem 3.1 (Rhee and Glynn 2015): the single term estimator.** Kahalé,
arXiv:2209.09581v1, §3.1 and Theorem 3.1, p.7: "Let `(Y_l, l ≥ 0)` be a sequence of
square-integrable random variables such that `E(Y_l)` has a limit `µ_Y` as `l` goes to infinity.
Consider a probability distribution `(p_l, l ≥ 0)` such that `p_l > 0` for `l ≥ 0`. Let `N ∈ ℕ`
be an integral random variable independent of `(Y_l, l ≥ 0)` such that `Pr(N = l) = p_l` for
`l ≥ 0`. … Set `Z := (Y_N − Y_{N−1})/p_N`, with `Y_{−1} := 0`. If
`Σ_{l=0}^∞ E((Y_l − Y_{l−1})²)/p_l` is finite then `Z` is square-integrable, `E(Z) = µ_Y`, and
`E(Z²) = Σ_{l=0}^∞ E((Y_l − Y_{l−1})²)/p_l`."

**Formalization Note.** `Y_l − Y_{l−1}` is `increment Y l` (`= Y_0` at `l = 0`). Independence of
`N` from the whole sequence is independence from the map `ω ↦ (Y_l(ω))_{l}` into `ℕ → ℝ` with the
product σ-algebra. Finiteness of the series of nonnegative terms is `Summable`. That `(p_l)` is a
probability distribution is not a separate hypothesis: `Pr(N = l) = p_l` for all `l` forces
`Σ p_l = 1`. -/
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ l, MemLp (Y l) 2 P) (μY : ℝ)
    (hμY : Tendsto (fun l => ∫ ω, Y l ω ∂P) atTop (𝓝 μY))
    (p : ℕ → ℝ) (hp_pos : ∀ l, 0 < p l)
    (N : Ω → ℕ) (hN : Measurable N) (hN_indep : IndepFun N (fun ω l => Y l ω) P)
    (hN_law : ∀ l, P {ω | N ω = l} = ENNReal.ofReal (p l))
    (hfin : Summable (fun l => (∫ ω, (increment Y l ω) ^ 2 ∂P) / p l)) :
    MemLp (fun ω => increment Y (N ω) ω / p (N ω)) 2 P ∧
    ∫ ω, increment Y (N ω) ω / p (N ω) ∂P = μY ∧
    ∫ ω, (increment Y (N ω) ω / p (N ω)) ^ 2 ∂P
      = ∑' l, (∫ ω, (increment Y l ω) ^ 2 ∂P) / p l := by sorry

end UnbiasedTimeAvg
