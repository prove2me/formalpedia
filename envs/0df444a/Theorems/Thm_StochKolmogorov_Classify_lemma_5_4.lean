-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_lemma_5_4
-- name    : StochKolmogorov.Classify.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:57.69484+00:00
-- url     : https://prove2.me/theorems/73c0fc13-000a-4b57-99a7-9695708f27a8
-- title:
--   Lemma 5.4, p. 24 — the time averages of (1+cᵀX)^{δ₁}(1+Σᵢ(|fᵢ|+gᵢ²)) have lim sup ≤ K̂ a.s., and (1/t)∫₀ᵗ Σᵢ cᵢXᵢgᵢ/(1+cᵀX) dEᵢ → 0 a.s.
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i$, $i = 1,\dots,n$ ($n \ge 1$), on $\mathbb R^n_+ = [0,\infty)^n$, with $E = \Gamma^\top B$ for a standard Brownian motion $B$ and $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$; $X^x$ denotes the solution started at $x$, and the coefficients satisfy Assumption 1.1 with the vector $c \in \mathbb R^{n,\circ}_+$ and the constant $\gamma_b > 0$ of (1.2). Let $\delta_0$ satisfy (3.2), and suppose Assumption 1.4 holds with $\delta_1 \le \delta_0$. Then:
--
--   1. there is $\widehat K > 0$ such that, for every $x \in \mathbb R^n_+$, almost surely
--   $$
--   \limsup_{t\to\infty}\frac1t\int_0^t(1+c^\top X^x(s))^{\delta_1}\Big(1+\sum_i(|f_i(X^x(s))|+|g_i(X^x(s))|^2)\Big)ds \le \widehat K;
--   $$
--   2. (5.17) for every $x \in \mathbb R^n_+$, almost surely
--   $$
--   \lim_{t\to\infty}\frac1t\int_0^t\frac{\sum_ic_iX^x_i(s)g_i(X^x(s))}{1+c^\top X^x(s)}\,dE_i(s) = 0 .
--   $$
--
--   Part 1 gives the tightness of the occupation measures (Lemma 5.7) and the uniform integrability needed in Lemma 5.6; part 2 is the martingale strong law used in (5.22).
--
--   **Formalization Note** The standing setting is carried by explicit hypotheses: `hn : 0 < n`, a family `X x` of strong solutions from every $x \in \mathbb R^n_+$ driven by one Brownian motion `B` (`IsSolutionFamily`), and `Assumption11 C c γb`. Coordinates are indexed by `Fin n` (0-based), and $\|x\| = \sum_i |x_i|$ is the $\ell^1$ norm `l1` of p. 4. The constant $\widehat K$ is chosen before $x$. The $\limsup \le \widehat K$ is written as: for every $\varepsilon > 0$, eventually $\int_0^t(\cdots)ds \le (\widehat K+\varepsilon)t$, with a lower Lebesgue integral of the nonnegative integrand. Because $dE_i = \sum_j\Gamma_{ji}dB_j$, the stochastic integral is $\sum_j J_j(t)$ with $J_j$ the Itô integral of $\sum_i c_iX_ig_i(X)\Gamma_{ji}/(1+c^\top X)$ against $B_j$; (5.17) is stated for every family $J$ of continuous versions of these Itô integrals (with respect to the completed Brownian filtration), so it does not depend on a choice of version. The paper's convention $\delta_1 \le \delta_0$ (Assumption 1.4, "without loss of generality") is the hypothesis `hδ₁`.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 5.4 and (5.17), p. 24

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem lemma_5_4 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (δ₁ : ℝ) (h14 : Assumption14 C δ₁) (hδ₁ : δ₁ ≤ δ₀) :
    (∃ Khat : ℝ, 0 < Khat ∧ ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ₁ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t)) ∧
    ∀ x ∈ orthant n, ∀ J : Fin n → ℝ≥0 → Ω → ℝ,
      (∀ j, (∀ ω, Continuous (fun t => J j t ω)) ∧
        HasBrownianItoIntegral P (completedBrownianPast P B (fun _ => x))
          (fun t ω => B t ω j) (fun t ω => itoIntegrand C c j (X x t ω)) (J j)) →
      ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => (∑ j, J j t ω) / (t : ℝ)) atTop (𝓝 0) := by sorry

end StochKolmogorov.Classify
