-- Prove2me | Theorems.Thm_TailRiskSharing_VaRTail_theorem2_var_tail_inf_convolution
-- name    : TailRiskSharing.VaRTail.theorem2_var_tail_inf_convolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:50.263276+00:00
-- url     : https://prove2.me/theorems/7051710b-7d01-4804-b028-561b3db1b7c5
-- title:
--   Theorem 2, p. 13 — VaR^L_α □ ρ(X) = ρ(X^[α]), its optimal allocation, the VaR^R limit, and the tail parameter α + ε
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and $L^0$ the set of all random variables. Let $\varepsilon\in(0,1)$ and let $\rho:L^0\to\mathbb R$ be a monetary (monotone and translation-invariant) $\varepsilon$-tail risk measure. Let $\alpha\in(0,1-\varepsilon)$. For $X\in L^0$ and a uniform random variable $U_X$ on $[0,1]$ with $F^{-1}_X(U_X)=X$ a.s., write
--   $$X^{[\alpha]}=X\,\mathbb 1_{\{U_X\le 1-\alpha\}}+\mathrm{VaR}^R_{\alpha+\varepsilon}(X)\,\mathbb 1_{\{U_X>1-\alpha\}}.$$
--   Then:
--
--   1. $\mathrm{VaR}^L_\alpha\,\square\,\rho(X)=\rho(X^{[\alpha]})$;
--   2. $(X-X^{[\alpha]},\,X^{[\alpha]})$ is an optimal allocation of $X$ for $(\mathrm{VaR}^L_\alpha,\rho)$;
--   3. $\displaystyle \mathrm{VaR}^R_\alpha\,\square\,\rho(X)=\lim_{\delta\downarrow 0}\rho\big(X^{[\alpha-\delta]}\big)$, the limit existing;
--   4. both $\mathrm{VaR}^R_\alpha\,\square\,\rho$ and $\mathrm{VaR}^L_\alpha\,\square\,\rho$ are monetary $(\alpha+\varepsilon)$-tail risk measures on $L^0$.
--
--   Parts 1–3 hold for every $X\in L^0$ and every choice of $U_X$. The theorem gives an explicit value and an explicit optimal allocation for risk sharing between a VaR agent and an agent with an arbitrary monetary tail risk measure, and shows that the representative agent's tail parameter is the sum $\alpha+\varepsilon$.
--
--   **Formalization Note** The inf-convolutions are valued in the extended reals; part 3 asserts convergence in the extended reals as $\delta\to0^+$, which states both existence of the limit and its value. In part 4, "monetary" and "$(\alpha+\varepsilon)$-tail" are the extended-real-valued versions of the definitions, required on $L^0$. The paper's risk measures may take the value $-\infty$; here $\rho$ is real-valued, which is the case in which Theorem 2 is applied (agents' risk measures in §2.3 are real-valued). The domain $\mathcal X$ is fixed to $L^0$.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 13, Theorem 2 (i)–(iv); proof pp. 13–15

import Mathlib
import Definitions.Def_TailRiskSharing_VaRTail_Setting

open MeasureTheory Filter Topology

namespace TailRiskSharing.VaRTail

theorem theorem2_var_tail_inf_convolution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (ρ : (Ω → ℝ) → ℝ) (hρm : IsMonetary P TailRiskSharing.VaRConv.L0 ρ) (hρt : IsTailRiskMeasure P TailRiskSharing.VaRConv.L0 ε ρ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε) :
    -- (i)
    (∀ X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ)), ∀ U : Ω → ℝ, IsQuantileUniform P X U →
      TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRL P α, ρ] X = ((ρ (cutAt P ε α X U) : ℝ) : EReal)) ∧
    -- (ii)
    (∀ X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ)), ∀ U : Ω → ℝ, IsQuantileUniform P X U →
      TailRiskSharing.VaRConv.IsOptimalAllocation TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRL P α, ρ] X ![X - cutAt P ε α X U, cutAt P ε α X U]) ∧
    -- (iii)
    (∀ X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ)), ∀ U : Ω → ℝ, IsQuantileUniform P X U →
      Tendsto (fun δ : ℝ => ((ρ (cutAt P ε (α - δ) X U) : ℝ) : EReal)) (𝓝[>] 0)
        (𝓝 (TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRR P α, ρ] X))) ∧
    -- (iv)
    (IsMonetaryE P TailRiskSharing.VaRConv.L0 (fun X => TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRR P α, ρ] X) ∧
      IsTailRiskMeasureE P TailRiskSharing.VaRConv.L0 (α + ε) (fun X => TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRR P α, ρ] X) ∧
      IsMonetaryE P TailRiskSharing.VaRConv.L0 (fun X => TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRL P α, ρ] X) ∧
      IsTailRiskMeasureE P TailRiskSharing.VaRConv.L0 (α + ε) (fun X => TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRL P α, ρ] X)) := by sorry

end TailRiskSharing.VaRTail
