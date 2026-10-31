-- Prove2me | Theorems.Thm_QiFixedDesign_Concentration_theorem_2
-- name    : QiFixedDesign.Concentration.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:00:50.532848+00:00
-- url     : https://prove2.me/theorems/8f4b3268-cf4d-42bb-ace4-5be7239d1968
-- title:
--   Theorem 2 — concentration of the surrogate residual distribution
-- statement:
--   Fix a natural-number dimension $p$, a deterministic sequence $x_i\in\mathbb R^p$, a true coefficient $\beta_0$, and a Borel probability law $\mu$ on $\mathbb R$ with mean zero. Suppose $a>1$, $A>1$ and $\int e^{|u|^a}\,\mu(du)=A<\infty$. Let $G_N=X_N^TX_N$, where $X_N$ contains the first $N$ feature rows, and suppose $G_N/N$ converges to a finite nonsingular matrix. Call $N$ admissible if $N>0$ and $G_N$ is nonsingular. Under the product training law $\mu^{\otimes N}$, put $Y_i=\beta_0^Tx_i+\omega_i$ and $\widehat\beta_N=G_N^{-1}X_N^TY$. Write $\widehat P_N(\beta)$ for the uniform empirical law of $Y_i-\beta^Tx_i$.
--
--   Fix any deterministic prediction vector $c\in\mathbb R^p$. For each training realization let $P_{\varepsilon'}(\omega)$ be the pushforward of $\mu$ by $u\mapsto u+(\beta_0-\widehat\beta_N(\omega))^Tc$. For every confidence $\eta\in(0,1)$ there exists one deterministic nonnegative sequence $(r_N)$ with $r_N\to0$ such that, for every admissible $N$,
--   $$\mu^{\otimes N}\{W_1(P_{\varepsilon'}(\omega),\widehat P_N(\widehat\beta_N(\omega)))\ge r_N\}\le\eta.$$
--   Radii may depend on the deterministic model, law and confidence, but not on the realized training vector. This is the whole Theorem 2: existence, convergence and the closed-tail probability bound simultaneously at every admissible sample size. There is no summability requirement on a confidence sequence and no assertion uniform over varying prediction vectors.
--
--   Differences from the source:
--   - encoding: coordinates and samples numbered from one → Fin p and Fin N numbered from zero, with natural-number dimension p; reason: the coordinate bijections preserve all sums and matrices; zero dimensions are not silently excluded
--   - encoding: probabilities and possibly infinite transport costs → nonnegative extended real measures and coupling costs; reason: infinite costs stay infinite and finite probabilities have their usual values
--   - encoding: Section 3 mean-zero iid innovations and deterministic fixed-design observations → product law on real training vectors, concrete responses, OLS residuals and pathwise shifted law; reason: the product measure is exactly the joint training law and the future innovation is integrated only after fixing training data
--   - encoding: full-rank design at the sample sizes under consideration and nonsingular normalized Gram limit → the bound holds at every positive nonsingular prefix, with GramLimit on the full sequence; reason: does not demand impossible full rank when N is smaller than p and does not discard any admissible sample size
--   - encoding: A is the finite exponential moment and innovations have mean zero → a nonnegative extended integral equals the finite real A, and the real first integral is zero; reason: light tails guarantee first and second integrability, so no default-zero integral changes an instance
--   - encoding: a sequence of Wasserstein-ball radii → a real sequence nonnegative at all indices, including the unused zero index; reason: radii are nonnegative by definition and extending unused indices does not alter the claim
--   - generalization: the Section 3 model has no intercept term → the deterministic design may include constant feature columns; reason: the OLS and concentration statements use full column rank and the Gram limit, not exclusion of constant columns; every source design is included with the same conclusions
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, Theorem 2, PDF/printed p. 17; proof (53)–(54), p. 21

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_ResidualLaw
import Definitions.Def_QiFixedDesign_Concentration_ShiftedLaw
import Definitions.Def_QiFixedDesign_Concentration_LightTail
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

theorem theorem_2 {p : ℕ} (x : ℕ → Fin p → ℝ) (β₀ : Fin p → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a A : ℝ) (hTail : LightTail μ a A) (hMean : ∫ u, u ∂μ = 0)
    (hDesign : GramLimit x)
    (c : Fin p → ℝ) (η : ℝ) (hη : 0 < η) (hη₁ : η < 1) :
    ∃ r : ℕ → ℝ, (∀ N, 0 ≤ r N) ∧ Tendsto r atTop (𝓝 0) ∧
      ∀ N : ℕ, admissible x N →
        Measure.pi (fun _ : Fin N => μ)
          {ω | ENNReal.ofReal (r N) ≤
            WassersteinDRO.Duality.wassersteinDistance 1
              (shiftedLaw μ x β₀ c ω) (fittedResidualLaw x β₀ ω)} ≤ ENNReal.ofReal η := by sorry

end QiFixedDesign.Concentration
