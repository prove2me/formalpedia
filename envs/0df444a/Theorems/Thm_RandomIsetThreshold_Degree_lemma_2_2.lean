-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_lemma_2_2
-- name    : RandomIsetThreshold.Degree.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:06:01.219205+00:00
-- url     : https://prove2.me/theorems/2e582563-08f3-4418-84a5-18489b23a60d
-- title:
--   Lemma 2.2 — both tails of the independence number, uniformly in bias
-- statement:
--   For every integer $r\ge2$ and $0<\eta\le1/2$, there are $d,\xi>0$ and a sequence $a_n\ge0$, depending only on $r,\eta$, with $a_n\to0$ as $n\to\infty$, such that for every $n\ge r$ and every $d/n^{r-1}\le p\le1-n^{-\xi}$,
--
--   $$\Pr\left(\alpha(H_{n,p})\notin\left[(1-\eta)r^{1/(r-1)}L,\ (1+\eta)r^{1/(r-1)}L\right]\right)\le a_n.$$
--
--   The same error sequence controls every permitted bias at each $n$, and both tails are included. Small $n\ge r$ are included rather than hidden behind an asymptotic threshold.
--
--   Differences from the source:
--   - encoding: vertices [n], all unordered r-sets, and real edge probabilities → Fin n, the subtype of r-element finsets, and unitInterval parameters; reason: order-preserving relabeling; interior biases are imposed or follow from the source regime
--   - encoding: constants with specified parameter dependencies → nested existential witnesses before the parameters on which they may not depend; reason: makes the source uniformity explicit without changing an instance
--   - encoding: the sequence γ_n(r,η) tends to zero → a nonnegative real sequence err with Tendsto atTop (nhds 0); reason: ordinary convergence of a sequence, chosen before p so that the bound is uniform
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 7, Lemma 2.2, equation (13); proof Appendix A.2, pp. 25–26

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_Hypergraph

open MeasureTheory
open scoped ENNReal BigOperators
universe u_lemma_2_2

namespace RandomIsetThreshold.Degree

theorem lemma_2_2
(r : ℕ) (hr : 2 ≤ r) (η : ℝ) (hη : 0 < η ∧ η ≤ 1 / 2) :
    ∃ d ξ : ℝ, 0 < d ∧ 0 < ξ ∧ ∃ err : ℕ → ℝ,
      (∀ n, 0 ≤ err n) ∧ Filter.Tendsto err Filter.atTop (nhds 0) ∧
      ∀ n : ℕ, r ≤ n → ∀ p : unitInterval, Regime n r p d ξ →
        (graphLaw n r p).real {G |
          (independenceNumber G : ℝ) ∉ Set.Icc
            ((1 - η) * rootFactor r * scale n r p)
            ((1 + η) * rootFactor r * scale n r p)} ≤ err n := by sorry

end RandomIsetThreshold.Degree
