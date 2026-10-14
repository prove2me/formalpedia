-- Prove2me | Theorems.Thm_QuantileSPQO_Rate_lemma_2
-- name    : QuantileSPQO.Rate.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:58.839331+00:00
-- url     : https://prove2.me/theorems/0ccb95e2-015c-4e34-ae11-c2da2c91329f
-- title:
--   Lemma 2 — the bias b_k(q_k, D_k, θ_k) of the SP estimator is O(c_k²) w.p.1 and in mean
-- statement:
--   Under the hypotheses of Lemma 1 (a run of SPQO with A1, A2 and A3(a)), let $b_k(q,D,\theta)$ be the bias of the simultaneous-perturbation gradient estimator,
--   $$
--   b_k(q_k,D_k,\theta_k)=E\Big[\frac{-I_k^++I_k^-}{2\bar c_k\Delta_k}\,\Big|\,\mathcal F_k\Big]+f(q_k;\theta_k)D_k+\nabla_\theta F(q_k;\theta_k).
--   $$
--   Then
--
--   1. almost surely there is a constant $C$ with $\|b_k(q_k,D_k,\theta_k)\|\le C c_k^2$ for all large $k$;
--   2. there is a constant $C$ with $E\big[\|b_k(q_k,D_k,\theta_k)\|\big]\le Cc_k^2$ for all large $k$.
--
--   That is, $b_k=O(c_k^2)$ w.p.1 and $E\|b_k\|=O(c_k^2)$. This bias bound is what lets the gradient recursion (21) track $-\nabla_\theta F/f$.
--
--   **Formalization Note** The conditional expectation is replaced by the explicit average over the $2^d$ sign vectors defined in the Setting file, which equals it almost surely under A2 and the sampling model. $O(\cdot)$ is the paper's one-sided notion (p. 11): eventually bounded by a constant times the rate. In part (i) the constant may depend on the sample path, as "w.p.1" allows; in part (ii) it does not depend on $k$. The expectation is a Lebesgue integral in $[0,\infty]$.
-- source:
--   Hu, Song and Fu, Quantile Optimization via Multiple Timescale Local Search for Black-box Functions, arXiv:2308.07607v1, p. 13, Lemma 2

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_QuantileSPQO_Rate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace QuantileSPQO.Rate

theorem lemma_2 {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hΘ : IsConstraintSet Θ) (hM : IsQuantileModel M Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA1 : A1 P M R) (hA2 : A2 P ℱ R) (hA3a : A3a β c) :
    (∀ᵐ ω ∂P, ∃ C : ℝ, ∀ᶠ k in atTop,
      ‖bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)‖ ≤ C * c k ^ 2) ∧
    (∃ C : ℝ, ∀ᶠ k in atTop,
      ∫⁻ ω, ‖bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)‖ₑ ∂P ≤ ENNReal.ofReal (C * c k ^ 2)) := by sorry

end QuantileSPQO.Rate
