-- Prove2me | Theorems.Thm_PrescAnalytics_ERM_lemma_1_comparison
-- name    : PrescAnalytics.ERM.lemma_1_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:41:27.89098+00:00
-- url     : https://prove2.me/theorems/045e8be6-d0ad-4f26-82df-9e7a720554e7
-- title:
--   Lemma 1 — ℜ̂_N(𝒢; S_N) ≤ L ℜ̂_N(F; S_N^x) and ℜ_N(𝒢) ≤ L ℜ_N(F) for costs L-Lipschitz in the ∞-norm
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be measurable spaces, $\mathcal F$ a class of decision rules $f:\mathcal X\to\mathbb R^d$, and $c(z;y)$ a cost that is $L$-Lipschitz in $z$ with respect to the $\infty$-norm, uniformly over $y$:
--   $$|c(z;y)-c(z';y)|\le L\max_{k=1,\dots,d}|z_k-z'_k|\qquad\text{for all }z,z'\in\mathbb R^d,\ y\in\mathcal Y,$$
--   with $L\ge0$. Let $\mathcal G=\{(x,y)\mapsto c(f(x);y):f\in\mathcal F\}$. Then:
--
--   1. for every $N$ and every sample $S_N=((x^1,y^1),\dots,(x^N,y^N))$, with $S_N^x=(x^1,\dots,x^N)$,
--   $$\widehat{\mathfrak R}_N(\mathcal G;S_N)\le L\,\widehat{\mathfrak R}_N(\mathcal F;S_N^x);$$
--   2. for every probability measure $\mu$ on $\mathcal X\times\mathcal Y$ and every $N$, if every $f\in\mathcal F$ is measurable, $\mathcal F$ is pointwise separable and $c$ is jointly measurable,
--   $$\mathfrak R_N(\mathcal G)\le L\,\mathfrak R_N(\mathcal F),$$
--   where $\mathfrak R_N(\mathcal G)$ samples $(x,y)$ i.i.d. from $\mu$ and $\mathfrak R_N(\mathcal F)$ samples $x$ i.i.d. from the marginal $\mu_X$ of $\mu$.
--
--   The left sides are univariate complexities, the right sides multivariate. This comparison lemma extends Ledoux and Talagrand's contraction principle to vector-valued classes with the $\infty$-norm and constant $1$; it is what lets the out-of-sample bound of Theorem 13 be stated in terms of the decision rules alone.
--
--   **Formalization Note** The paper writes the Lipschitz condition as $\sup_{z\ne z'}(c(z;y)-c(z';y))/\max_k|z_k-z'_k|\le L<\infty$, which is the two-sided bound above (swap $z,z'$); the Lean norm on `Fin d → ℝ` is this max. Complexities are in `EReal` (empirical) and $[0,\infty]$ (marginal), with $0\cdot(\pm\infty)=0$; when $L=0$ the cost does not depend on $z$ and both sides are $0$ for nonempty $\mathcal F$. The paper states part 2 with no measurability assumptions; the Lean adds measurable rules, a pointwise separable class and a measurable cost, the conventions under which the expectations are defined.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, pp. 39–40, Lemma 1

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Basic

namespace PrescAnalytics.ERM

open MeasureTheory

/-- Lemma 1 (pp. 39–40), multivariate comparison lemma. If the cost `c(z; y)` is `L`-Lipschitz in
the decision `z ∈ ℝ^d` with respect to the `∞`-norm, uniformly over `y`, then for the cost class
`𝒢 = {(x, y) ↦ c(f(x); y) : f ∈ F}`:
(i) on every sample `S_N`, `ℜ̂_N(𝒢; S_N) ≤ L ℜ̂_N(F; S_N^x)`;
(ii) for i.i.d. sampling from `μ`, `ℜ_N(𝒢) ≤ L ℜ_N(F)`, where `ℜ_N(F)` samples only the
covariates, i.e. from the marginal `μ_X` of `μ`. Part (ii) carries the measurability conventions
(measurable rules, pointwise separable class, measurable cost) under which the expectations exist. -/
theorem lemma_1_comparison {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {d : ℕ}
    (F : Set (X → Fin d → ℝ)) (c : (Fin d → ℝ) → Y → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖) :
    (∀ (N : ℕ) (s : Fin N → X × Y),
        empRademacherR (costClass c F) s ≤ (L : EReal) * empRademacher F (fun i => (s i).1)) ∧
    (∀ (μ : Measure (X × Y)) [IsProbabilityMeasure μ] (N : ℕ),
        (∀ f ∈ F, Measurable f) → IsPointwiseSeparable F → Measurable (Function.uncurry c) →
        margRademacherR μ N (costClass c F) ≤
          ENNReal.ofReal L * margRademacher (μ.map Prod.fst) N F) := by sorry

end PrescAnalytics.ERM
