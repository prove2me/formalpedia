-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_lemma_3_3
-- name    : StochKolmogorov.Classify.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:33:02.2876+00:00
-- url     : https://prove2.me/theorems/d06bfb5c-d118-4869-8970-f4bf6df5b96c
-- title:
--   Lemma 3.3, p. 14 — every invariant probability measure µ satisfies ∫(1+cᵀx)^{δ₀}(1+Σᵢ(|fᵢ|+gᵢ²))dµ ≤ H₂, and the bracket of (1.2) integrates to 0
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i$, $i = 1,\dots,n$ ($n \ge 1$), on $\mathbb R^n_+ = [0,\infty)^n$, with $E = \Gamma^\top B$ for a standard Brownian motion $B$ and $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$; $X^x$ denotes the solution started at $x$, and the coefficients satisfy Assumption 1.1 with the vector $c \in \mathbb R^{n,\circ}_+$ and the constant $\gamma_b > 0$ of (1.2). Let $\delta_0$ satisfy (3.2), and let $H_2 > 0$ be a constant as in (3.8) of Lemma 3.2:
--   $$
--   \mathbb E_x\int_0^t (1+c^\top X(s))^{\delta_0}\Big[1+\sum_i(|f_i(X(s))|+|g_i(X(s))|^2)\Big]ds \le H_2\big((1+c^\top x)^{\delta_0}+t\big),\qquad x \in \mathbb R^n_+,\ t > 0.
--   $$
--   Then every invariant probability measure $\mu$ of $X$ satisfies
--   $$
--   \int_{\mathbb R^n_+}(1+c^\top x)^{\delta_0}\Big(1+\sum_i(|f_i(x)|+|g_i(x)|^2)\Big)\mu(dx) \le H_2
--   $$
--   and
--   $$
--   \int_{\mathbb R^n_+}\Big(\frac{\sum_i c_ix_if_i(x)}{1+c^\top x} - \frac12\frac{\sum_{i,j}\sigma_{ij}c_ic_jx_ix_jg_i(x)g_j(x)}{(1+c^\top x)^2}\Big)\mu(dx) = 0 .
--   $$
--
--   The first bound makes every Lyapunov exponent $\lambda_i(\mu)$ well defined; the identity is used in (5.21) to show that $\ln(1+c^\top X(t))/t \to 0$.
--
--   **Formalization Note** The standing setting is carried by explicit hypotheses: `hn : 0 < n`, a family `X x` of strong solutions from every $x \in \mathbb R^n_+$ driven by one Brownian motion `B` (`IsSolutionFamily`), and `Assumption11 C c γb`. Coordinates are indexed by `Fin n` (0-based), and $\|x\| = \sum_i |x_i|$ is the $\ell^1$ norm `l1` of p. 4. The constant $H_2$ of Lemma 3.2 enters as any $H_2 > 0$ satisfying (3.8), stated with lower Lebesgue integrals of the nonnegative integrand. The first integral is a lower Lebesgue integral (so it cannot be satisfied by a non-integrable integrand); the integrability of the bracket of (1.2), implicit in the paper's second display, is stated as part of the conclusion.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 3.3, p. 14 (with (3.8) of Lemma 3.2, p. 14)

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem lemma_3_3 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (H₂ : ℝ) (hH₂ : 0 < H₂)
    (h38 : ∀ x ∈ orthant n, ∀ t : ℝ, 0 < t →
      ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal (growthWeight C c δ₀ (X x s.toNNReal ω))) ∂P
        ≤ ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t)))
    (μ : Measure (SDEState n)) (hμ : IsInvariant P X μ) :
    ∫⁻ y, ENNReal.ofReal (growthWeight C c δ₀ y) ∂μ ≤ ENNReal.ofReal H₂ ∧
      Integrable (cBracket C c) μ ∧ ∫ y, cBracket C c y ∂μ = 0 := by sorry

end StochKolmogorov.Classify
