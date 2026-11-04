-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_short_time_positivity
-- name    : StochKolmogorov.Classify.short_time_positivity
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T09:10:30.586525+00:00
-- url     : https://prove2.me/theorems/8d61f125-e155-4f2a-be22-c5d7f7ef1514
-- title:
--   Short-time positivity: a coordinate bounded away from $0$ stays above a level $\beta>0$ on $[0,T]$ with high probability, uniformly on $\|x\|_1\le R$
-- statement:
--   Let $X^x$ solve the stochastic Kolmogorov system under Assumption 1.1 (with vector $c$ and constant $\gamma_b$). For all $R$, $T>0$ and $\varepsilon_1,\varepsilon_2>0$ there is $\beta>0$ such that for every coordinate $i$ and every $x\in\mathbb R^n_+$ with $\|x\|_1\le R$ and $x_i>\varepsilon_2$,
--
--   $$\mathbb P\big(X^x_i(t)>\beta\ \text{for all } t\le T\big)>1-\varepsilon_1 .$$
--
--   Role: once the path enters the far set $\{\|y\|_1<R,\ y_i>\eta\ \text{for some } i\notin\operatorname{supp}\mu\}$, it keeps a non-sink coordinate above $\beta$ for a fixed time with probability $>1/2$; combined with the grid estimate this bounds the probability of ever entering the far set (paper (5.19), used in (5.31)-(5.32)).
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, Ann. Appl. Probab. 28 (2018), https://arxiv.org/abs/1704.06984v1, Section 5, display (5.19) (consequence of (5.15) and Appendix B: continuity of the solution in probability, uniformly on compact sets of initial values), used in the proof of Lemma 5.9, pp. 26-27

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem short_time_positivity {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    ∀ R T : ℝ, 0 < T → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → ∃ β : ℝ, 0 < β ∧
      ∀ i, ∀ x ∈ orthant n, l1 x ≤ R → ε₂ < x i →
        1 - ε₁ < (P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T → β < X x t ω i}).toReal := by sorry

end StochKolmogorov.Classify
