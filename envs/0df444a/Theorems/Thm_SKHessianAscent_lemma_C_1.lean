-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_C_1
-- name    : SKHessianAscent.lemma_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-23T01:24:16.896837+00:00
-- url     : https://prove2.me/theorems/010a9c47-eb5c-488a-9510-56766b123bbb
-- title:
--   Lemma C.1 — approximate rejection sampling with unknown normalization: total-variation error and acceptance probability of Algorithm 4
-- statement:
--   There is a universal constant $K_N$ such that the following holds. Let $P\ll Q$ be probability measures with $\frac{dP}{dQ}\propto R$. Suppose that Algorithm 4 is run with $\widetilde Q$, $\widetilde R$, parameters $C_1,C_2$, failure probability $\delta'\in(0,1)$ and $N\ge K_NC_1^2\log(1/\delta')$ initial samples, satisfying:
--
--   1. (Sampling error) $\widetilde Q$ is a distribution such that $\mathrm{TV}(\widetilde Q,Q)\le\varepsilon_{\mathrm{sample}}$.
--   2. (Tails of ratio) With $C(\varepsilon)=\inf\{C:\mathbf E_Q(\frac{dP}{dQ}\wedge C)\ge1-\varepsilon\}$, $C_1\ge C(1/2)\vee1$ and $C_2\ge C(\varepsilon_{\mathrm{weight}})$.
--   3. (Ratio error) $G_1,G_2$ are events such that $G_1\subseteq\{\widetilde R/R\in[0,e^{\varepsilon_{\mathrm{ratio}}}]\}$ and $G_1\cap G_2\subseteq\{\widetilde R/R\in[e^{-\varepsilon_{\mathrm{ratio}}},e^{\varepsilon_{\mathrm{ratio}}}]\}$, with $\widetilde Q(G_1^c)\le\delta_1$ and $P(G_2^c)\le\delta_2$ (these probabilities include the randomness of $\widetilde R$).
--
--   Then, letting $\widehat P$ be the output distribution, with probability $\ge1-\delta'$ over the $N$ initial samples,
--   $$\mathrm{TV}(\widehat P,P)\le\varepsilon_{\mathrm{weight}}+\delta_2+384C_1C_2(\delta_1+\varepsilon_{\mathrm{ratio}}+\varepsilon_{\mathrm{sample}}),$$
--   and if $\varepsilon_{\mathrm{weight}}+\delta_2+96C_1C_2(\delta_1+\varepsilon_{\mathrm{ratio}}+\varepsilon_{\mathrm{sample}})\le\frac12$, the acceptance probability is at least $\frac1{192C_1C_2}$.
--
--   **Formalization Note** "$N=\Omega(C_1^2\log(1/\delta'))$ for appropriate constant" is $N\ge K_NC_1^2\log(1/\delta')$ for a universal $K_N$. The events $G_1,G_2$ are subsets of the product of the sample space with the randomness $\theta$ of $\widetilde R$; $\widetilde Q(G_1^c)$ and $P(G_2^c)$ are their probabilities under $\widetilde Q\otimes\nu$ and $P\otimes\nu$. $\widetilde R/R\le e^{\varepsilon}$ is written $\widetilde R\le e^{\varepsilon}R$. The quantile is the empirical quantile of the values $\widetilde R(X_i,\theta_i)$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Appendix C, Algorithm 4 and Lemma C.1, pp. 49–50 ([DLSS26a, Lemma 3.8])

import Mathlib
import Definitions.Def_SKHessianAscent_Rejection

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace SKHessianAscent

theorem lemma_C_1 :
    ∃ KN : ℝ, 0 < KN ∧
      ∀ (X Θ : Type) [MeasurableSpace X] [MeasurableSpace Θ] (P Q Qt : Measure X) (ν : Measure Θ)
        [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure Qt]
        [IsProbabilityMeasure ν] (R : X → ℝ) (Rt : X → Θ → ℝ) (Z : ℝ),
        P ≪ Q → 0 < Z → Measurable R → Measurable (Function.uncurry Rt) → (∀ x θ, 0 ≤ Rt x θ) →
        (∀ᵐ x ∂Q, R x = Z * (P.rnDeriv Q x).toReal) →
        ∀ (C₁ C₂ εs εw εr δ₁ δ₂ δ' : ℝ) (G₁ G₂ : Set (X × Θ)),
          MeasurableSet G₁ → MeasurableSet G₂ →
          0 ≤ εs → 0 < εw → 0 ≤ εr → 0 ≤ δ₁ → 0 ≤ δ₂ → 0 < δ' → δ' < 1 →
          tvMeas Qt Q ≤ εs →
          max (ratioCutoff P Q (1 / 2)) 1 ≤ C₁ → ratioCutoff P Q εw ≤ C₂ →
          (∀ z ∈ G₁, Rt z.1 z.2 ≤ Real.exp εr * R z.1) →
          (∀ z ∈ G₁ ∩ G₂, Real.exp (-εr) * R z.1 ≤ Rt z.1 z.2) →
          (Qt.prod ν) G₁ᶜ ≤ ENNReal.ofReal δ₁ → (P.prod ν) G₂ᶜ ≤ ENNReal.ofReal δ₂ →
          ∀ N : ℕ, KN * C₁ ^ 2 * Real.log (1 / δ') ≤ N →
            (Measure.pi fun _ : Fin N => Qt.prod ν)
                {s | ¬ (
                  tvMeas (rejOut Qt ν Rt (8 * C₂ *
                      empQuantile (1 - 1 / (6 * C₁)) fun i => Rt (s i).1 (s i).2)) P ≤
                    εw + δ₂ + 384 * C₁ * C₂ * (δ₁ + εr + εs) ∧
                  (εw + δ₂ + 96 * C₁ * C₂ * (δ₁ + εr + εs) ≤ 1 / 2 →
                    ENNReal.ofReal (1 / (192 * C₁ * C₂)) ≤
                      acceptProb Qt ν Rt (8 * C₂ *
                        empQuantile (1 - 1 / (6 * C₁)) fun i => Rt (s i).1 (s i).2)))} ≤
              ENNReal.ofReal δ' := by sorry

end SKHessianAscent
