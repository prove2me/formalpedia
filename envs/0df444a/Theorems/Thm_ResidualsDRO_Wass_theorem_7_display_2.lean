-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_theorem_7_display_2
-- name    : ResidualsDRO.Wass.theorem_7_display_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:14:13.586502+00:00
-- url     : https://prove2.me/theorems/8a594219-600f-4cee-a0a6-3bb03d07a021
-- title:
--   Proof of Theorem 7, display 2, p. 15 — P{d_{W,p}(P*_n(x), P_{Y|X=x}) > κ^(2)_{p,n}(α)} ≤ α/2 (corrected κ^(2))
-- statement:
--   On a probability space $(\Omega,\mathbb P)$, let the errors $\varepsilon^1,\dots,\varepsilon^n$ ($n\ge1$) be i.i.d. with law $P_\varepsilon$ on $\mathbb R^{d_y}$ ($d_y\ge1$). Let $1\le p<a$ with $\mathbb E[\exp(\|\varepsilon\|^a)]<\infty$ (Assumption 1), $p\ne d_y/2$, and let $c_1,c_2>0$ be constants for which the bound of Lemma 2 holds at the sample size $n$ and the covariate $x$. Then for every $\alpha\in(0,1)$,
--   $$\mathbb P\big\{d_{W,p}(P^*_n(x),P_{Y\mid X=x})>\kappa^{(2)}_{p,n}(\alpha)\big\}\le\frac\alpha2,$$
--   where $P^*_n(x)=\frac1n\sum_i\delta_{f^*(x)+\varepsilon^i}$, $P_{Y\mid X=x}$ is the law of $f^*(x)+\varepsilon$, and $\kappa^{(2)}_{p,n}(\alpha)$ is the second term of the radius (10) built from $\log(2c_1\alpha^{-1})$.
--
--   This is the sampling part of the radius: the true empirical distribution is within $\kappa^{(2)}_{p,n}(\alpha)$ of the conditional distribution except with probability $\alpha/2$.
--
--   **Formalization Note** The paper prints $\log(c_1\alpha^{-1})$ in $\kappa^{(2)}_{p,n}(\alpha)$; with that choice Lemma 2 gives only the bound $\alpha$, and the display would not follow. The paper's stated derivation ("setting the r.h.s. of the inequality in Lemma 2 to $\alpha/2$") gives $\log(2c_1\alpha^{-1})$, which is used. Assumption 1, $p\ne d_y/2$ and the i.i.d. hypothesis are the hypotheses under which the paper invokes Lemma 2; Lemma 2's conclusion itself is a hypothesis.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 15, proof of Theorem 7, second display (with (10) and Lemma 2, p. 13)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_ResidualsDRO_Wass_Setting
import Definitions.Def_ResidualsDRO_Wass_Radius

open MeasureTheory ProbabilityTheory

namespace ResidualsDRO.Wass

/-- Proof of Theorem 7, display 2, p. 15. On a probability space `(Ω, P)`, let the errors
`ε¹, …, εⁿ` (`n ≥ 1`) be i.i.d. with law `P_ε` on `ℝ^{d_y}` (`d_y ≥ 1`), let Assumption 1 hold
(`a > p ≥ 1`), `p ≠ d_y/2`, and let `c₁, c₂ > 0` be constants for which the conclusion of
Lemma 2 holds at `n` and the covariate `x`. Then for `α ∈ (0, 1)`,
`P{d_{W,p}(P*_n(x), P_{Y|X=x}) > κ^{(2)}_{p,n}(α)} ≤ α/2`,
with `κ^{(2)}_{p,n}(α)` the corrected term of (10) (built from `log(2c₁α⁻¹)`; the paper prints
`log(c₁α⁻¹)`, for which Lemma 2 only gives `α`). -/
theorem theorem_7_display_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {dx dy n : ℕ} (hdy : 1 ≤ dy) (hn : 1 ≤ n)
    (p a : ℝ) (hp : 1 ≤ p) (hpdy : p ≠ (dy : ℝ) / 2)
    (Pε : Measure (EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure Pε]
    (hA1 : Assumption1 Pε p a)
    (fstar : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (eps : Fin n → Ω → EuclideanSpace ℝ (Fin dy)) (heps_meas : ∀ i, Measurable (eps i))
    (heps_indep : iIndepFun eps P) (heps_law : ∀ i, P.map (eps i) = Pε)
    (x : EuclideanSpace ℝ (Fin dx))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hL2 : Lemma2Bound P Pε fstar eps x dy p a c₁ c₂)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    P {ω | ENNReal.ofReal (kappa2 c₁ c₂ a p dy n α) <
        WassersteinDRO.Duality.wassersteinDistance p (trueEmpirical fstar (fun i => eps i ω) x)
          (condLaw Pε fstar x)} ≤
      ENNReal.ofReal (α / 2) := by sorry

end ResidualsDRO.Wass
