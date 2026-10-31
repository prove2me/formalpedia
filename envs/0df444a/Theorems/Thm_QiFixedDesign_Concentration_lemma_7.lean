-- Prove2me | Theorems.Thm_QiFixedDesign_Concentration_lemma_7
-- name    : QiFixedDesign.Concentration.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:00:44.438973+00:00
-- url     : https://prove2.me/theorems/f45f479b-18fc-4b7b-9c5d-7af32968457d
-- title:
--   Lemma 7 — shifted-law concentration, with shrinking radius
-- statement:
--   Fix a natural-number dimension $p$, a deterministic sequence $x_i\in\mathbb R^p$, a true coefficient $\beta_0$, and a Borel probability law $\mu$ on $\mathbb R$ with mean zero. Suppose $a>1$, $A>1$ and $\int e^{|u|^a}\,\mu(du)=A<\infty$. Let $G_N=X_N^TX_N$, where $X_N$ contains the first $N$ feature rows, and suppose $G_N/N$ converges to a finite nonsingular matrix. Call $N$ admissible if $N>0$ and $G_N$ is nonsingular. Under the product training law $\mu^{\otimes N}$, put $Y_i=\beta_0^Tx_i+\omega_i$ and $\widehat\beta_N=G_N^{-1}X_N^TY$. Write $\widehat P_N(\beta)$ for the uniform empirical law of $Y_i-\beta^Tx_i$.
--
--   Fix any deterministic prediction vector $c\in\mathbb R^p$, including $c=0$, and any finite variance upper bound $\kappa\ge\int u^2\,\mu(du)$. For each training vector define $P_{\varepsilon'}(\omega)$ to be the pushforward of $\mu$ under $u\mapsto u+(\beta_0-\widehat\beta_N(\omega))^Tc$. For every $\eta\in(0,1)$ put $r_{3,N}=\sqrt{\kappa c^TG_N^{-1}c/\eta}$. Then $r_{3,N}\to0$ and for every admissible $N$,
--   $$\mu^{\otimes N}\{W_1(\mu,P_{\varepsilon'}(\omega))\ge r_{3,N}\}\le\eta.$$
--   The bound is preserved as printed, including its false $c=0$ case: the radius is zero and the event is certain. The finding is recorded in INSIGHTS.yaml; neither the threshold inequality nor the allowed prediction vectors have been changed.
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
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, Lemma 7, (46), PDF/printed p. 19; (18), p. 12

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_ShiftedLaw
import Definitions.Def_QiFixedDesign_Concentration_Radii
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

theorem lemma_7 {p : ℕ} (x : ℕ → Fin p → ℝ) (β₀ : Fin p → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a A : ℝ) (hTail : LightTail μ a A) (hMean : ∫ u, u ∂μ = 0)
    (hDesign : GramLimit x)
    (c : Fin p → ℝ) (κ : ℝ) (hκ : (∫ u, u ^ 2 ∂μ) ≤ κ)
    (η : ℝ) (hη : 0 < η) (hη₁ : η < 1) :
    Tendsto (radiusThree x c κ η) atTop (𝓝 0) ∧
    ∀ N : ℕ, admissible x N →
      Measure.pi (fun _ : Fin N => μ)
        {ω | ENNReal.ofReal (radiusThree x c κ η N) ≤
          WassersteinDRO.Duality.wassersteinDistance 1 μ (shiftedLaw μ x β₀ c ω)} ≤
        ENNReal.ofReal η := by sorry

end QiFixedDesign.Concentration
