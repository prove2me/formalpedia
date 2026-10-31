-- Prove2me | Theorems.Thm_QiFixedDesign_Concentration_lemma_6
-- name    : QiFixedDesign.Concentration.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:00:52.712649+00:00
-- url     : https://prove2.me/theorems/86bcd206-6e47-491b-89f8-16658891f4f3
-- title:
--   Lemma 6 — empirical versus OLS residual law, with shrinking radius
-- statement:
--   Fix a natural-number dimension $p$, a deterministic sequence $x_i\in\mathbb R^p$, a true coefficient $\beta_0$, and a Borel probability law $\mu$ on $\mathbb R$ with mean zero. Suppose $a>1$, $A>1$ and $\int e^{|u|^a}\,\mu(du)=A<\infty$. Let $G_N=X_N^TX_N$, where $X_N$ contains the first $N$ feature rows, and suppose $G_N/N$ converges to a finite nonsingular matrix. Call $N$ admissible if $N>0$ and $G_N$ is nonsingular. Under the product training law $\mu^{\otimes N}$, put $Y_i=\beta_0^Tx_i+\omega_i$ and $\widehat\beta_N=G_N^{-1}X_N^TY$. Write $\widehat P_N(\beta)$ for the uniform empirical law of $Y_i-\beta^Tx_i$.
--
--   Let $\kappa\in\mathbb R$ be any upper bound for $\sigma^2=\int u^2\,\mu(du)$. For every $\eta\in(0,1)$ define $r_{2,N}=\sqrt{p\kappa/N}/\eta$. Then $r_{2,N}\to0$, and for every admissible $N$,
--   $$\mu^{\otimes N}\{W_1(\widehat P_N(\beta_0),\widehat P_N(\widehat\beta_N))\ge r_{2,N}\}\le\eta.$$
--   The same deterministic sequence is used at every sample size; the confidence factor is outside the square root. The source does not explicitly exclude $p=0$; under that convention this lemma also has a zero-radius failure, documented separately.
--
--   Differences from the source:
--   - encoding: coordinates and samples numbered from one → Fin p and Fin N numbered from zero, with natural-number dimension p; reason: the coordinate bijections preserve all sums and matrices; zero dimensions are not silently excluded
--   - encoding: probabilities and possibly infinite transport costs → nonnegative extended real measures and coupling costs; reason: infinite costs stay infinite and finite probabilities have their usual values
--   - encoding: Section 3 mean-zero iid innovations and deterministic fixed-design observations → product law on real training vectors, concrete responses, OLS residuals and pathwise shifted law; reason: the product measure is exactly the joint training law and the future innovation is integrated only after fixing training data
--   - encoding: full-rank design at the sample sizes under consideration and nonsingular normalized Gram limit → the bound holds at every positive nonsingular prefix, with GramLimit on the full sequence; reason: does not demand impossible full rank when N is smaller than p and does not discard any admissible sample size
--   - encoding: A is the finite exponential moment and innovations have mean zero → a nonnegative extended integral equals the finite real A, and the real first integral is zero; reason: light tails guarantee first and second integrability, so no default-zero integral changes an instance
--   - encoding: the standing Section 3 assumptions and the variance bound introduced after Lemma 4 → GramLimit, mean zero and an arbitrary real upper bound kappa for the actual second moment; reason: these are the source standing assumptions and its allowed variance bound, not the desired concentration conclusion
--   - generalization: the Section 3 model has no intercept term → the deterministic design may include constant feature columns; reason: the OLS and concentration statements use full column rank and the Gram limit, not exclusion of constant columns; every source design is included with the same conclusions
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, Lemma 6, (39), PDF/printed p. 17; proof pp. 18–19

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_ResidualLaw
import Definitions.Def_QiFixedDesign_Concentration_Radii
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

theorem lemma_6 {p : ℕ} (x : ℕ → Fin p → ℝ) (β₀ : Fin p → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a A : ℝ) (hTail : LightTail μ a A) (hMean : ∫ u, u ∂μ = 0)
    (hDesign : GramLimit x)
    (κ : ℝ) (hκ : (∫ u, u ^ 2 ∂μ) ≤ κ)
    (η : ℝ) (hη : 0 < η) (hη₁ : η < 1) :
    Tendsto (radiusTwo p κ η) atTop (𝓝 0) ∧
    ∀ N : ℕ, admissible x N →
      Measure.pi (fun _ : Fin N => μ)
        {ω | ENNReal.ofReal (radiusTwo p κ η N) ≤
          WassersteinDRO.Duality.wassersteinDistance 1
            (residualLaw x β₀ β₀ ω) (fittedResidualLaw x β₀ ω)} ≤ ENNReal.ofReal η := by sorry

end QiFixedDesign.Concentration
