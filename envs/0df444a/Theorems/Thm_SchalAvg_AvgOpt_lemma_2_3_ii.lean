-- Prove2me | Theorems.Thm_SchalAvg_AvgOpt_lemma_2_3_ii
-- name    : SchalAvg.AvgOpt.lemma_2_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:36.651427+00:00
-- url     : https://prove2.me/theorems/8b57f7a3-11e9-42bb-9c7d-44cf516d9bea
-- title:
--   Lemma 2.3(ii) — Fatou's lemma for weakly converging probability measures with w̲(x) = liminf_{n→∞, y→x} w_n(y)
-- statement:
--   Let $X$ be an arbitrary metric space with its Borel σ-algebra, and let $\mu_n$, $\mu$ be probability measures on $X$ with $\mu_n \to \mu$ **weakly** ($\int h \, d\mu_n \to \int h \, d\mu$ for every bounded continuous $h$). Let $w_n$ be measurable nonnegative functions on $X$ and
--   $$\underline w(x) = \liminf_{n \to \infty,\ y \to x} w_n(y), \qquad x \in X.$$
--   Then
--   $$\int \underline w \, d\mu \ \le\ \liminf_{n \to \infty} \int w_n \, d\mu_n.$$
--
--   Under weak convergence the pointwise lower limit of Lemma 2.3(i) is not enough; the lower limit must also be taken over nearby points. This lemma is the limit step in the proof of Proposition 3.5 under Condition (W).
--
--   **Formalization Note.** Weak convergence is convergence in Mathlib's topology on `ProbabilityMeasure X`. The functions take values in $[0, \infty]$. The joint lower limit is taken along the product filter `atTop ×ˢ 𝓝 x` (which includes $y = x$); in a metric space it agrees with the sequential lower limit $\inf\{\liminf_n w_n(y_n) : y_n \to x\}$, and $\underline w$ is lower semicontinuous, hence Borel.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), p. 166, Lemma 2.3(ii)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

theorem lemma_2_3_ii {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure X) (μs : ℕ → ProbabilityMeasure X)
    (hμ : Tendsto μs atTop (𝓝 μ))
    (w : ℕ → X → ℝ≥0∞) (hw : ∀ n, Measurable (w n)) :
    ∫⁻ x, liminf (fun p : ℕ × X => w p.1 p.2) (atTop ×ˢ 𝓝 x) ∂(μ : Measure X) ≤
      liminf (fun n => ∫⁻ x, w n x ∂(μs n : Measure X)) atTop := by sorry

end SchalAvg.AvgOpt
