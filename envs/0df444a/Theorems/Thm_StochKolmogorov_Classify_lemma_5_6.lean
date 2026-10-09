-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_lemma_5_6
-- name    : StochKolmogorov.Classify.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:42.244997+00:00
-- url     : https://prove2.me/theorems/2bab9b28-7ed9-45f2-926b-7dbe89f0d6ad
-- title:
--   Lemma 5.6, p. 25 — along a sample path with bounded weighted time averages, Π̃_{T_k} → π weakly implies ∫h dΠ̃_{T_k} → ∫h dπ for continuous h of growth below the weight
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i$, $i = 1,\dots,n$ ($n \ge 1$), on $\mathbb R^n_+ = [0,\infty)^n$, with $E = \Gamma^\top B$ for a standard Brownian motion $B$ and $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$; $X^x$ denotes the solution started at $x$, and the coefficients satisfy Assumption 1.1 with the vector $c \in \mathbb R^{n,\circ}_+$ and the constant $\gamma_b > 0$ of (1.2). Let $\delta_0$ satisfy (3.2), and suppose Assumption 1.4 holds with $\delta_1 \le \delta_0$. For every $x \in \mathbb R^n_+$ and every sample path of $X^x$ that stays in $\mathbb R^n_+$, suppose the path satisfies
--   $$
--   \limsup_{t\to\infty}\frac1t\int_0^t(1+c^\top X(s))^{\delta_1}\Big(1+\sum_i(|f_i(X(s))|+|g_i(X(s))|^2)\Big)ds \le \widehat K
--   $$
--   for some constant $\widehat K$, and that $\widetilde\Pi_{T_k}$ converges weakly to an invariant probability measure $\pi$ of $X$ along a sequence of times $T_k \to \infty$. Then for every function $h$ continuous on $\mathbb R^n_+$ with
--   $$
--   |h(x)| < K_h(1+c^\top x)^{\delta}\Big(1+\sum_i(|f_i(x)|+|g_i(x)|^2)\Big),\qquad x \in \mathbb R^n_+,
--   $$
--   for a constant $K_h > 0$ and an exponent $\delta \in [0,\delta_1)$, the function $h$ is $\pi$-integrable and
--   $$
--   \int_{\mathbb R^n_+} h(x)\,\widetilde\Pi_{T_k}(dx) \longrightarrow \int_{\mathbb R^n_+} h(x)\,\pi(dx) .
--   $$
--
--   This upgrades weak convergence of occupation measures to convergence of the time averages of the unbounded functions $f_i - \sigma_{ii}g_i^2/2$ and of the bracket of (1.2), which is how Lyapunov exponents enter the pathwise analysis.
--
--   **Formalization Note** The standing setting is carried by explicit hypotheses: `hn : 0 < n`, a family `X x` of strong solutions from every $x \in \mathbb R^n_+$ driven by one Brownian motion `B` (`IsSolutionFamily`), and `Assumption11 C c γb`. Coordinates are indexed by `Fin n` (0-based), and $\|x\| = \sum_i |x_i|$ is the $\ell^1$ norm `l1` of p. 4. The page states the lemma for "a sample path of X"; here it is stated for every path that stays in $\mathbb R^n_+$ (the property holds almost surely by Lemma 3.1), uniformly over $\widehat K$, the sequence, $\pi$ and $h$. The page's "$(T_k)_{k\in\mathbb N} \subset \mathbb R^n_+$" is a typo for a sequence of times; the Lean takes real times. The $\pi$-integrability of $h$ is added to the conclusion so that the limit is not the default value of a non-integrable integral. $\delta_1 \le \delta_0$ is the paper's convention in Assumption 1.4.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 5.6, p. 25

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem lemma_5_6 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (δ₁ : ℝ) (h14 : Assumption14 C δ₁) (hδ₁ : δ₁ ≤ δ₀) :
    ∀ x ∈ orthant n, ∀ ω : Ω, (∀ t, X x t ω ∈ orthant n) → ∀ Khat : ℝ,
      (∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ₁ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t)) →
      ∀ (Ts : ℕ → ℝ) (π : Measure (SDEState n)), Tendsto Ts atTop atTop → IsInvariant P X π →
      (∀ h : SDEState n →ᵇ ℝ,
        Tendsto (fun k => ∫ y, h y ∂(occ X x (Ts k) ω)) atTop (𝓝 (∫ y, h y ∂π))) →
      ∀ (h : SDEState n → ℝ) (Kh δ : ℝ), ContinuousOn h (orthant n) → 0 < Kh → 0 ≤ δ →
        δ < δ₁ → (∀ y ∈ orthant n, |h y| < Kh * growthWeight C c δ y) →
        Integrable h π ∧
          Tendsto (fun k => ∫ y, h y ∂(occ X x (Ts k) ω)) atTop (𝓝 (∫ y, h y ∂π)) := by sorry

end StochKolmogorov.Classify
