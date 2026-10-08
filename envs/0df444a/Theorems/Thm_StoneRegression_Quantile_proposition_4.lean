-- Prove2me | Theorems.Thm_StoneRegression_Quantile_proposition_4
-- name    : StoneRegression.Quantile.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:59.853443+00:00
-- url     : https://prove2.me/theorems/afe9a9f2-4042-40f6-b719-dadfbcf7338f
-- title:
--   Proposition 4, p. 609 — under (1)–(3), Σᵢ|Wₙᵢ(X)| I{|f(Xᵢ) − f(X)| > ε} → 0 in probability for every Borel f
-- statement:
--   Let $\{W_n\}$ be a sequence of (jointly Borel) weights satisfying conditions (1)–(3): there are $C\ge1$ and $D\ge1$ with
--   $$E\sum_i|W_{ni}(X)|f(X_i)\le C\,Ef(X)\ \ (f\ge0 \text{ Borel}),\qquad P\Big(\sum_i|W_{ni}(X)|\le D\Big)=1,$$
--   for all $n\ge1$, and $\sum_i|W_{ni}(X)|I_{\{\|X_i-X\|>a\}}\to0$ in probability for every $a>0$. Let $f$ be any Borel function on $\mathbb R^d$. Then for every $\varepsilon>0$
--   $$\sum_i |W_{ni}(X)|\,I_{\{|f(X_i)-f(X)|>\varepsilon\}}\to0\quad\text{in probability.}$$
--
--   Condition (3) says the weights concentrate near $X$ in distance; the proposition upgrades this to concentration on sample points where an arbitrary Borel function $f$ is close to $f(X)$. In the proof of Proposition 13 it is applied to the conditional quantile function $f=L^Y(p\mid\cdot)$.
--
--   **Formalization Note.** No integrability is assumed on $f$, as on the page. The weight functions are assumed jointly Borel.
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 4, p. 609 (§10)

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Proposition 4, p. 609: under (1)–(3), for every Borel `f` on `ℝᵈ` and every `ε > 0`,
`∑ᵢ |W_{ni}(X)| I{|f(Xᵢ) − f(X)| > ε} → 0` in probability. No integrability is assumed on `f`. -/
theorem proposition_4 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (hW : StoneRegression.Criterion.MeasurableWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ StoneRegression.Criterion.Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ StoneRegression.Criterion.Cond2 μ W D) (h3 : StoneRegression.Criterion.Cond3 μ W)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f) :
    ∀ ε : ℝ, 0 < ε → TendstoInMeasure (StoneRegression.Criterion.xLaw μ)
      (fun n ω => ∑ i : Fin n, |StoneRegression.Criterion.wAt W n ω i| *
        (if ε < |f (ω (i.val + 1)) - f (ω 0)| then 1 else 0)) atTop (fun _ => 0) := by sorry

end StoneRegression.Quantile
