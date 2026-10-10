-- Prove2me | Theorems.Thm_TailRiskSharing_RobustVaR_theorem6_robust_var_comonotonic
-- name    : TailRiskSharing.RobustVaR.theorem6_robust_var_comonotonic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:02:55.494719+00:00
-- url     : https://prove2.me/theorems/834542f4-b99e-426c-9a96-0d6a1e818d86
-- title:
--   Theorem 6, p. 31 — comonotonic inf-convolution of Wasserstein-robust VaRs, (36)–(37), optimal allocation (X, 0, …, 0)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $X\in L^\infty$ and $\Lambda\in\{L,R\}$. For a risk measure $\rho$ and $\delta>0$, $[\rho]^1_\delta(X)=\sup\{\rho(Y):Y\in L^\infty,\ W_1(Y,X)\le\delta\}$ is its robust version over the order-$1$ Wasserstein ball, and $\boxplus$ is the inf-convolution over comonotonic allocations $\mathbb A^+_n(X)$. Consider $n\ge1$ agents.
--
--   1. If $0<\delta_1\le\dots\le\delta_n$ and $\alpha\in(0,1)$, then
--
--   $$
--   \mathop{\boxplus}_{i=1}^n[\mathrm{VaR}^\Lambda_\alpha]^1_{\delta_i}(X)=[\mathrm{VaR}^\Lambda_\alpha]^1_{\delta_1}(X)+\sum_{i=2}^n\frac{\delta_i}{\alpha}.
--   $$
--
--   2. If $1>\alpha_1\ge\dots\ge\alpha_n>0$ and $\delta>0$, then
--
--   $$
--   \mathop{\boxplus}_{i=1}^n[\mathrm{VaR}^\Lambda_{\alpha_i}]^1_{\delta}(X)=[\mathrm{VaR}^\Lambda_{\alpha_1}]^1_{\delta}(X)+\sum_{i=2}^n\frac{\delta}{\alpha_i}.
--   $$
--
--   3. In either setting, the allocation $(X,0,\dots,0)$ is an optimal comonotonic allocation.
--
--   When agents assess risk by Wasserstein-robust VaR and must share a loss comonotonically, it is optimal to give the whole loss to one agent: the one least sensitive to uncertainty (smallest $\delta_i$) when the levels agree, or the one least sensitive to risk (largest $\alpha_i$) when the radii agree.
--
--   **Formalization Note** The $n=m+1$ agents are indexed by `Fin (m+1)`; the paper's agent $1$ is index $0$, and $\sum_{i=2}^n$ is the sum over the successors `i.succ`, `i : Fin m`. The orderings are `Monotone δs` and `Antitone αs`. The constrained inf-convolution is `EReal`-valued. The domain is $L^\infty$, as in the paper's §8.2, and the same $\Lambda$ is used by all agents.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 31, Theorem 6, (36)–(37); proof pp. 31–33

import Mathlib
import Definitions.Def_TailRiskSharing_RobustVaR_Setting
import Definitions.Def_TailRiskSharing_RobustVaR_Wasserstein

namespace TailRiskSharing.RobustVaR

open MeasureTheory

theorem theorem6_robust_var_comonotonic {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (X : Ω → ℝ) (hX : X ∈ TailRiskSharing.TailConv.Linf P) (Λ : TailRiskSharing.VaRConv.Side) (m : ℕ) :
    (∀ (δs : Fin (m + 1) → ℝ) (α : ℝ), 0 < δs 0 → Monotone δs → 0 < α → α < 1 →
      TailRiskSharing.ComonoConv.comonoInfConv P (TailRiskSharing.TailConv.Linf P) (fun i => robust P 1 (δs i) (TailRiskSharing.VaRConv.VaRS P Λ α)) X =
          ((robust P 1 (δs 0) (TailRiskSharing.VaRConv.VaRS P Λ α) X + ∑ i : Fin m, δs i.succ / α : ℝ) : EReal) ∧
        IsOptimalComonoAllocation P (TailRiskSharing.TailConv.Linf P) (fun i => robust P 1 (δs i) (TailRiskSharing.VaRConv.VaRS P Λ α)) X
          (fun i => if i = 0 then X else 0)) ∧
    (∀ (αs : Fin (m + 1) → ℝ) (δ : ℝ), Antitone αs → αs 0 < 1 → 0 < αs (Fin.last m) → 0 < δ →
      TailRiskSharing.ComonoConv.comonoInfConv P (TailRiskSharing.TailConv.Linf P) (fun i => robust P 1 δ (TailRiskSharing.VaRConv.VaRS P Λ (αs i))) X =
          ((robust P 1 δ (TailRiskSharing.VaRConv.VaRS P Λ (αs 0)) X + ∑ i : Fin m, δ / αs i.succ : ℝ) : EReal) ∧
        IsOptimalComonoAllocation P (TailRiskSharing.TailConv.Linf P) (fun i => robust P 1 δ (TailRiskSharing.VaRConv.VaRS P Λ (αs i))) X
          (fun i => if i = 0 then X else 0)) := by sorry

end TailRiskSharing.RobustVaR
