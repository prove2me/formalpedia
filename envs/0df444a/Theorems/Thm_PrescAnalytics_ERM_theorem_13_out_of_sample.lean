-- Prove2me | Theorems.Thm_PrescAnalytics_ERM_theorem_13_out_of_sample
-- name    : PrescAnalytics.ERM.theorem_13_out_of_sample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:41:45.389989+00:00
-- url     : https://prove2.me/theorems/48886c94-55ec-4bf8-93ed-6be83762cc75
-- title:
--   Theorem 13 — out-of-sample guarantees (26), (27) for every decision rule in F, costs in [0, c̄] and L-Lipschitz
-- statement:
--   Let $\mu$ be a probability measure on $\mathcal X\times\mathcal Y$ (covariates $X$, uncertainty $Y$), and let $\mathcal F$ be a pointwise separable class of measurable decision rules $z(\cdot):\mathcal X\to\mathbb R^{d}$. Let the cost $c(z;y)$ be jointly measurable, bounded and equi-Lipschitz in $z$:
--   $$0\le c(z;y)\le\bar c,\qquad |c(z;y)-c(z';y)|\le L\,\|z-z'\|_\infty\qquad\text{for all }z,z'\in\mathbb R^{d},\ y\in\mathcal Y,$$
--   with $L\ge0$. Let $N\ge1$, $\delta>0$, and let $S_N=((x^1,y^1),\dots,(x^N,y^N))$ be an i.i.d. sample from $\mu$, with covariate part $S_N^x=(x^1,\dots,x^N)$. Then each of the following events occurs with probability at least $1-\delta$:
--   $$\mathbb E[c(z(X);Y)]\le\frac1N\sum_{i=1}^N c(z(x^i);y^i)+\bar c\sqrt{\frac{\log(1/\delta)}{2N}}+L\,\mathfrak R_N(\mathcal F)\qquad\forall z\in\mathcal F,\tag{26}$$
--   $$\mathbb E[c(z(X);Y)]\le\frac1N\sum_{i=1}^N c(z(x^i);y^i)+3\bar c\sqrt{\frac{\log(2/\delta)}{2N}}+L\,\widehat{\mathfrak R}_N(\mathcal F;S_N^x)\qquad\forall z\in\mathcal F.\tag{27}$$
--   Here $\mathfrak R_N(\mathcal F)$ is the marginal multivariate Rademacher complexity over i.i.d. covariate samples from the marginal $\mu_X$, and $\widehat{\mathfrak R}_N(\mathcal F;S_N^x)$ the empirical one on the observed covariates. In particular, both bounds hold for an empirical risk minimizer $\hat z_N(\cdot)\in\arg\min_{z(\cdot)\in\mathcal F}\frac1N\sum_i c(z(x^i);y^i)$.
--
--   The theorem bounds the true out-of-sample cost of any decision rule in the class, uniformly, by the quantity minimized in empirical risk minimization plus confidence terms that do not depend on the rule, for multivariate decisions.
--
--   **Formalization Note** The paper assumes only $\sup c\le\bar c$; with that alone (26) is false (take $\mathcal F=\{x\mapsto0\}$, $c(z;y)=y$, $Y$ uniform on $\{-1,+1\}$, $N=1$, $\delta=1/5$: the bound fails with probability $1/2$), so the Lean adds $0\le c$ and keeps every printed constant. The printed Lipschitz denominator $\|z_k-z'_k\|_\infty$ is read as $\|z-z'\|_\infty$, the Lean sup norm on `Fin d → ℝ`. The undefined $\delta',\delta''$ are $\delta$, as in the i.i.d. case of the paper's Theorem 21. Each "with probability at least $1-\delta$" is stated as: the set of samples on which the inequality fails for some $z\in\mathcal F$ has outer $\mu^N$-measure at most $\delta$. (26) is written as $\max(0,\mathbb E-\hat{\mathbb E}-\bar c\sqrt{\cdot})\le L\,\mathfrak R_N(\mathcal F)$ in $[0,\infty]$ and (27) in `EReal`, both equivalent to the real inequalities, with $0\cdot\infty=0$. Measurability of the rules and of $c$ and pointwise separability of $\mathcal F$ are the added measurability conventions. Covariate and uncertainty spaces are general measurable spaces; decisions are unconstrained, $\mathcal Z=\mathbb R^d$, as in §8.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, p. 39, Theorem 13, Eqs. (26), (27) (δ′ = δ″ = δ from p. 52, Theorem 21, IID case; proof p. 41)

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Basic

namespace PrescAnalytics.ERM

open MeasureTheory

/-- Theorem 13 (p. 39), with the corrected hypotheses `0 ≤ c ≤ c̄` and `δ' = δ'' = δ` (i.i.d. case of
Theorem 21). Let `μ` be a probability measure on `𝒳 × 𝒴`, `F` a pointwise separable class of
measurable decision rules `𝒳 → ℝ^d`, `c(z; y)` a jointly measurable cost with values in `[0, c̄]` that
is `L`-Lipschitz in `z` for the `∞`-norm, uniformly in `y`; `N ≥ 1`, `δ > 0`. Then, for i.i.d.
samples `S_N ∼ μ^N`, each of the following fails, for some `z ∈ F`, only on a set of outer measure
at most `δ`:
(26) `E[c(z(X); Y)] ≤ (1/N) Σ_i c(z(x^i); y^i) + c̄ √(log(1/δ)/(2N)) + L ℜ_N(F)` for all `z ∈ F`,
(27) `E[c(z(X); Y)] ≤ (1/N) Σ_i c(z(x^i); y^i) + 3c̄ √(log(2/δ)/(2N)) + L ℜ̂_N(F; S_N^x)` for all
`z ∈ F`, where `ℜ_N(F)` is taken over i.i.d. covariate samples from the marginal `μ_X`. -/
theorem theorem_13_out_of_sample {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {d : ℕ}
    (μ : Measure (X × Y)) [IsProbabilityMeasure μ]
    (F : Set (X → Fin d → ℝ)) (hF_meas : ∀ f ∈ F, Measurable f) (hF_sep : IsPointwiseSeparable F)
    (c : (Fin d → ℝ) → Y → ℝ) (hc_meas : Measurable (Function.uncurry c))
    (cbar L : ℝ) (hc_bdd : ∀ (z : Fin d → ℝ) (y : Y), 0 ≤ c z y ∧ c z y ≤ cbar)
    (hL : 0 ≤ L) (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖)
    (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin N => μ)
        {s | ∃ f ∈ F, ENNReal.ofReal L * margRademacher (μ.map Prod.fst) N F <
          ENNReal.ofReal (expCost μ c f - empCost s c f
            - cbar * Real.sqrt (Real.log (1 / δ) / (2 * N)))} ≤ ENNReal.ofReal δ ∧
    (Measure.pi fun _ : Fin N => μ)
        {s | ∃ f ∈ F, (L : EReal) * empRademacher F (fun i => (s i).1) <
          ((expCost μ c f - empCost s c f
            - 3 * cbar * Real.sqrt (Real.log (2 / δ) / (2 * N)) : ℝ) : EReal)} ≤ ENNReal.ofReal δ := by sorry

end PrescAnalytics.ERM
