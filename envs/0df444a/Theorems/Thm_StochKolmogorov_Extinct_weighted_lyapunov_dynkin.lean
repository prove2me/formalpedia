-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_weighted_lyapunov_dynkin
-- name    : StochKolmogorov.Extinct.weighted_lyapunov_dynkin
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T17:31:30.727879+00:00
-- url     : https://prove2.me/theorems/43452533-0b68-43b6-8bd2-ac536cedc3e9
-- title:
--   Weighted Dynkin inequality for $U_\theta$: $\mathbb{E}[e^{\int_0^t r(X_s)ds}U_\theta(X_t)]\le U_\theta(x)$
-- statement:
--   Let $X^x$ solve the stochastic Kolmogorov system of Assumption 1.1 from $x\in\mathbb{R}^n_{++}$, let $\delta_0$ be as in (3.5), let $\hat p_i\in(0,\delta_0)$ for $i\in\operatorname{supp}\mu$ with $\sum_{i\in\operatorname{supp}\mu}\hat p_i\le\delta_0$, $\check p,\theta\in(0,\delta_0)$, and $U_\theta=\sum_{i\notin\operatorname{supp}\mu}U_i^\theta$ with $U_i(x)=(1+c^\top x)\,x_i^{\check p}/\prod_{j\in\operatorname{supp}\mu}x_j^{\hat p_j}$. For every continuous rate $r$ bounded below with
--   $$r(z)\le\theta\max\Big(\gamma_b-H,\;-\big(\tfrac{\sum_i c_iz_if_i(z)}{1+c^\top z}-\tfrac12\tfrac{\sum_{i,j}\sigma_{ij}c_ic_jz_iz_jg_i(z)g_j(z)}{(1+c^\top z)^2}+\gamma_b\sum_i(|f_i(z)|+g_i(z)^2)\big)\Big)\quad(z\in\mathbb{R}^n_+),$$
--   $$\mathbb{E}\Big[e^{\int_0^t r(X^x_s)\,ds}\,U_\theta(X^x_t)\Big]\le U_\theta(x)\qquad(t\ge0).$$
--
--   Role: the weighted Lyapunov (Dynkin) inequality behind the one-step supermartingale estimate (5.11)-(5.12): the generator bound $\mathcal{L}U_\theta\le-r\,U_\theta$ on the open orthant (from (5.6) and (3.5)) turns into an expectation inequality for the clocked process.
--
--   **Formalization Note**: the rate $r$ is a free continuous function dominated by the generator bound, so the statement covers the specific rates used in Section 5 at once.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, Ann. Appl. Probab. 28 (2018), https://arxiv.org/abs/1704.06984, Section 5, eq. (5.6) with Dynkin's formula, p. 23

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem weighted_lyapunov_dynkin {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (hphat : (∀ i ∈ supp mu, 0 < phat i ∧ phat i < δ₀) ∧
      (∑ i ∈ supp mu, phat i) ≤ δ₀)
    (pcheck : ℝ) (hpcheck : 0 < pcheck ∧ pcheck < δ₀) (θ : ℝ) (hθ : 0 < θ ∧ θ < δ₀)
    (r : SDEState n → ℝ) (hr : Continuous r) (K : ℝ) (hK : ∀ z, -K ≤ r z)
    (hrle : ∀ z ∈ orthant n, r z ≤ θ * max (γb - Hconst C c γb δ₀)
      (-(cBracket C c z + γb * ∑ i, (|C.f i z| + C.g i z ^ 2))))
    (x : SDEState n) (hx : x ∈ openOrthant n) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (∫ s in (0 : ℝ)..(t : ℝ), r (X x s.toNNReal ω)) *
        Utheta c mu phat pcheck θ (X x t ω)) ∂P ≤
      ENNReal.ofReal (Utheta c mu phat pcheck θ x) := by sorry

end StochKolmogorov.Extinct
