-- Prove2me | Theorems.Thm_QuantileMDP_lemma_2
-- name    : QuantileMDP.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:02.464006+00:00
-- url     : https://prove2.me/theorems/0bfd40da-aa7f-40b2-a099-f72d502fbc16
-- title:
--   Lemma 2 — the quantile of $\sum_i X_iY_i$ solves $\max_q\min_{i:q_i\neq1}Q_{q_i}(X_i\mid Y_i=1)$ (corrected: strict quantile budget in OPT)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\iota=\{1,\dots,n\}$ a finite index set. Let $X_1,\dots,X_n$ be real random variables, each taking finitely many values, and let $Y_1,\dots,Y_n$ be random variables with values in $\{0,1\}$ such that $\sum_{i=1}^nY_i=1$ everywhere. Put $p_i=P(Y_i=1)$, and let $Q_{q}(X_i\mid Y_i=1)$ be the $q$-quantile of the conditional distribution of $X_i$ given $Y_i=1$. Then for every $\tau\in[0,1]$,
--
--   $$
--   Q_\tau\Bigl(\sum_{i=1}^nX_iY_i\Bigr)\;=\;\sup_{q}\ \min_{i\in\{i\,:\,q_i\neq1\}}Q_{q_i}(X_i\mid Y_i=1),
--   $$
--
--   the supremum being over $q\in[0,1]^n$ with $\sum_{i=1}^np_iq_i<\tau$ or $\sum_{i=1}^np_iq_i=0$; the supremum is attained by some such $q$.
--
--   The lemma expresses the quantile of a mixture through the quantiles of its components. It plays for quantiles the role that linearity of expectation plays in the classical MDP: it is what makes the backward recursion of Theorem 1 possible.
--
--   **Formalization Note** The conditional law is $P(\cdot\mid Y_i=1)$ pushed forward by $X_i$; when $p_i=0$ it is the zero measure (whose quantile is $+\infty$ for $q>0$ and $-\infty$ for $q=0$), and the optimizer drops such a component at no cost by $q_i=1$.
--
--   Differences from the source:
--   - correction: budget $\sum_ip_iq_i\le\tau$ → $\sum_ip_iq_i<\tau$ or $\sum_ip_iq_i=0$; reason: the printed statement is false — $X_1\equiv0$, $X_2\equiv10$, $Y_1\sim$ Bernoulli$(1/2)$, $Y_2=1-Y_1$, $\tau=1/2$: $q=(1,0)$ costs $1/2\le1/2$ and gives $10$, while $Q_{1/2}(X_1Y_1+X_2Y_2)=0$; at $\tau=1$ the printed $q=(1,\dots,1)$ also leaves the minimum empty.
--   - reading: $Q_{q_i}(X_i\mid Y_i=1)$ for $p_i=0$ (undefined on the page) → the quantile of the zero measure; reason: such a component can be removed at zero cost by $q_i=1$, so the value is that of the components with $p_i>0$.
--   - encoding: random variables → measurable functions on a probability space, "discrete" → finite range; reason: the paper's own definition of discrete ("take values on a finite set").
--   - encoding: max and min → supremum and infimum in the extended reals, with a separate clause that some feasible $q$ attains the supremum; reason: that clause is what the maximum asserts; the minimum over an empty index set is $+\infty$.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §3.2, Lemma 2 (9), p.12

import Mathlib
import Definitions.Def_QuantileMDP_quantile
import Definitions.Def_QuantileMDP_opt

open MeasureTheory ProbabilityTheory

namespace QuantileMDP

/-- Lemma 2 (corrected budget): for finitely-valued random variables `X_i` and binary `Y_i` with
`∑ Y_i = 1`, `Q_τ(∑ X_i Y_i)` equals the value of `max_q min_{i : q_i ≠ 1} Q_{q_i}(X_i | Y_i = 1)`
over `q ∈ [0,1]^n` with `∑ p_i q_i < τ` or `∑ p_i q_i = 0`, where `p_i = P(Y_i = 1)`, and the
maximum over `q` is attained.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §3.2, Lemma 2 (9),
p.12.

**Formalization Note** The printed budget `∑ p_i q_i ≤ τ` is replaced by the corrected one of
`opt` (counterexample: `X_1 ≡ 0`, `X_2 ≡ 10`, `Y_1 ~ Bernoulli(1/2)`, `Y_2 = 1 - Y_1`, `τ = 1/2`).
The conditional law of `X_i` given `Y_i = 1` is `(P[|Y_i = 1]).map (X_i)`; when `p_i = 0` it is the
zero measure, a component the optimizer drops at no cost by `q_i = 1`. -/
theorem lemma_2 {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hXfin : ∀ i, (Set.range (X i)).Finite) (hY : ∀ i, Measurable (Y i))
    (hY01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (hYsum : ∀ ω, ∑ i, Y i ω = 1)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    quantile (P.map (fun ω => ∑ i, X i ω * Y i ω)) τ =
        opt (fun i => (P {ω | Y i ω = 1}).toReal)
          (fun i q => quantile ((P[|{ω | Y i ω = 1}]).map (X i)) q) τ ∧
      OptAttained (fun i => (P {ω | Y i ω = 1}).toReal)
        (fun i q => quantile ((P[|{ω | Y i ω = 1}]).map (X i)) q) τ := by sorry

end QuantileMDP
