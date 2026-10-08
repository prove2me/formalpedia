-- Prove2me | Theorems.Thm_StochApproxDyn_Attractor_measure_limitSet_subset_ge
-- name    : StochApproxDyn.Attractor.measure_limitSet_subset_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:46:24.883659+00:00
-- url     : https://prove2.me/theorems/9f0a2eea-02aa-43bd-bd77-07a884cdf586
-- title:
--   Theorem 7.3 (second statement) — $P(L(X)\subset A)\ge(1-w(t,\delta,T))\,P(\exists s\ge t: X(s)\in U)$
-- statement:
--   Let $\Phi$ be a semiflow on a **locally compact** metric space $M$ and let $A\subset M$ be an attractor of $\Phi$ with basin $B(A)$. Let $U\subset M$ be an open set, relatively compact, with $\overline U\subset B(A)$. Then there exist numbers $T>0$ and $\delta>0$, depending only on $U$ (and on $\Phi$ and $A$), such that for every process $X$ on a probability space $(\Omega,\mathcal F,P)$ satisfying the standing assumptions of Section 7 with a function $w$, and every $t\ge0$,
--   $$P\big(L(X)\subset A\big)\ \ge\ \big(1-w(t,\delta,T)\big)\,P\big(\exists s\ge t:\ X(s)\in U\big).$$
--
--   This is the quantitative half of Theorem 7.3: the probability of converging to $A$ is bounded below by the probability of visiting a compact part of the basin after time $t$, discounted by the probability bound $w(t,\delta,T)$ in condition (24). When $w(t,\delta,T)\ge1$ the bound is trivial; it is informative for $t$ large.
--
--   **Formalization Note** $T$ and $\delta$ are chosen before the probability space, the process, $w$ and $t$, so they cannot depend on any of them. Probabilities are in `ℝ≥0∞`, and the factor $1-w(t,\delta,T)$ is `ENNReal.ofReal (1 - w t δ T)`, which is $0$ when $w>1$ (the real inequality is then trivial as well). The event $\{L(X)\subset A\}$ and the hitting event are measured by $P$ as an outer measure; no measurability hypothesis on them is added. The inequality is asserted for every $t\ge0$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), pp. 31–32, Section 7.1, Theorem 7.3 (second statement)

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics
import Definitions.Def_StochApproxDyn_Attractor_Process

open scoped NNReal ENNReal
open MeasureTheory

universe u v

namespace StochApproxDyn.Attractor

/-- Theorem 7.3, second statement (Benaïm 1999, pp. 31–32). The numbers `T, δ` depend only on
`Φ`, `A` and `U`: they are chosen before the probability space, the process and `w`. -/
theorem measure_limitSet_subset_ge {M : Type u} [MetricSpace M] [LocallyCompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (Φ : Flow ℝ≥0 M) (A : Set M) (hA : StochApproxDyn.LimitSet.IsAttractor Φ A)
    (U : Set M) (hU : IsOpen U) (hUc : IsCompact (closure U)) (hUB : closure U ⊆ StochApproxDyn.LimitSet.basin Φ A) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ (Ω : Type v) (m0 : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
        ∀ (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M) (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0),
          SatisfiesStandingAssumption Φ P ℱ X w →
          ∀ t : ℝ≥0,
            ENNReal.ofReal (1 - (w t δ T : ℝ)) * P {ω | ∃ s : ℝ≥0, t ≤ s ∧ X s ω ∈ U} ≤
              P {ω | StochApproxDyn.LimitSet.limitSet (fun s => X s ω) ⊆ A} := by sorry

end StochApproxDyn.Attractor
