-- Prove2me | Theorems.Thm_SabanisEuler_LpConv_lp_convergence
-- name    : SabanisEuler.LpConv.lp_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T00:33:59.396421+00:00
-- url     : https://prove2.me/theorems/2be29e32-7402-4605-9c3b-a5f123f0211f
-- title:
--   Theorem 1 — Lp-convergence of explicit Euler-type schemes for all p < p₀
-- statement:
--   Let $(\Omega,\{\mathcal F_t\}_{t\ge0},\mathcal F,P)$ be a filtered probability space with right-continuous filtration, $W$ a $d_1$-dimensional Wiener martingale, $T>0$, and $p_0,p_1\ge2$. Let $b(t,x)\in\mathbb R^d$ and $\sigma(t,x)\in\mathbb R^{d\times d_1}$ be Borel measurable, and let $X$ solve
--   $$dX(t)=b(t,X(t))\,dt+\sigma(t,X(t))\,dW(t),\qquad t\in[0,T],\tag{2.1}$$
--   with an $\mathcal F_0$-measurable initial value $X(0)$. For every $n\ge1$ let $b_n,\sigma_n$ be Borel measurable and let $X_n$ solve the explicit Euler-type scheme
--   $$dX_n(t)=b_n(t,X_n(\kappa_n(t)))\,dt+\sigma_n(t,X_n(\kappa_n(t)))\,dW(t),\qquad t\in[0,T],\tag{2.2}$$
--   with the same initial value $X(0)$, where $\kappa_n(t)=\lfloor nt\rfloor/n$. Suppose A-1–A-5 and B-1–B-3 hold with $\alpha\in(0,1/2]$. Then for every $0<p<p_0$,
--   $$\lim_{n\to\infty}\sup_{0\le t\le T}\mathbb E\big[|X(t)-X_n(t)|^p\big]=0.$$
--
--   The theorem covers every sequence of coefficients $b_n,\sigma_n$ satisfying B-1–B-3, including the tamed coefficients of the paper's Models 1 and 2, and gives $\mathcal L^p$-convergence of explicit schemes for SDEs with superlinearly growing drift and diffusion coefficients under a local monotonicity condition, for every $p$ below the moment order $p_0$ of the coercivity condition.
--
--   **Formalization Note** The solutions $X$ and $X_n$ are hypotheses, all defined on one probability space with one Wiener process and one initial value. The exponent is restricted to $p>0$, the paper's convention for $\mathcal L^p$. Expectations and the supremum over $t$ are taken in $[0,\infty]$, and the limit is taken there.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, p. 5, Theorem 1

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_SabanisEuler_LpConv_Conditions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open SabanisEuler.Shared

namespace SabanisEuler.LpConv

open EthierKurtz

/-- Sabanis (2016), arXiv:1308.1796v4, p. 5, Theorem 1: under A-1–A-5 and B-1–B-3 with
`α ∈ (0, 1/2]`, the scheme (2.2) converges to the solution of (2.1) in `𝓛^p`:
`lim_{n → ∞} sup_{0 ≤ t ≤ T} 𝔼[|X(t) - Xₙ(t)|^p] = 0` for all `0 < p < p₀`. -/
theorem lp_convergence
    {d d₁ : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (W : ℝ≥0 → Ω → SDEState d₁) (hW : IsWienerMartingale P ℱ W)
    (T : ℝ≥0) (hT : 0 < T)
    (p₀ p₁ : ℝ) (hp₀ : 2 ≤ p₀) (hp₁ : 2 ≤ p₁)
    (b : ℝ≥0 × SDEState d → SDEState d) (σ : ℝ≥0 × SDEState d → Diffusion d d₁)
    (hb : Measurable b) (hσ : Measurable σ)
    (bₙ : ℕ → ℝ≥0 × SDEState d → SDEState d) (σₙ : ℕ → ℝ≥0 × SDEState d → Diffusion d d₁)
    (hbₙ : ∀ n : ℕ, 1 ≤ n → Measurable (bₙ n)) (hσₙ : ∀ n : ℕ, 1 ≤ n → Measurable (σₙ n))
    (ξ : Ω → SDEState d) (hξ : Measurable[ℱ 0] ξ)
    (hA1 : CondA1 T b) (hA2 : CondA2 T b) (hA3 : CondA3 T p₁ b σ) (hA4 : CondA4 T p₀ b σ)
    (hA5 : CondA5 P p₀ ξ)
    (α : ℝ) (hα : 0 < α ∧ α ≤ 1 / 2)
    (hB1 : CondB1 T p₀ b σ bₙ σₙ)
    (hB2 : CondB2 T α b σ bₙ σₙ)
    (hB3 : CondB3 T p₀ bₙ σₙ)
    (X : ℝ≥0 → Ω → SDEState d) (hX : IsSolution P ℱ W T ξ b σ X)
    (Xₙ : ℕ → ℝ≥0 → Ω → SDEState d)
    (hXₙ : ∀ n : ℕ, 1 ≤ n → IsSchemeSolution P ℱ W T ξ bₙ σₙ n (Xₙ n)) :
    ∀ p : ℝ, 0 < p → p < p₀ → Tendsto
      (fun n : ℕ => ⨆ t ∈ Set.Icc (0 : ℝ≥0) T, ∫⁻ ω, ‖X t ω - Xₙ n t ω‖ₑ ^ p ∂P)
      atTop (𝓝 0) := by sorry

end SabanisEuler.LpConv
