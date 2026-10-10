-- Prove2me | Theorems.Thm_TailRiskSharing_ComonoConv_theorem4_comonotonic_inf_convolution
-- name    : TailRiskSharing.ComonoConv.theorem4_comonotonic_inf_convolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:35.661188+00:00
-- url     : https://prove2.me/theorems/d426633b-bda4-4d2f-9ab1-954337374c4b
-- title:
--   Theorem 4 (i)–(ii), pp. 20–21 — ⊞ρᵢ(X) = ⊞ρ*ᵢ(X_ε), and ⊞ρᵢ is an ε-tail risk measure, ε = ⋁εᵢ
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and $n\ge 1$. For $i=1,\dots,n$ let $\rho_i$ be an $\varepsilon_i$-tail risk measure on $L^0$ for some $\varepsilon_i\in(0,1)$, and put
--   $$\varepsilon=\bigvee_{i=1}^n\varepsilon_i=\max_{1\le i\le n}\varepsilon_i .$$
--   Let $\rho_i^*$ be an $\varepsilon$-generator of $\rho_i$: a law-invariant risk measure with $\rho_i(X)=\rho_i^*(X_\varepsilon)$ for all $X$. Then:
--
--   1. for every $X\in L^0$ and every quantile uniform $U_X$ of $X$, with $X_\varepsilon=F_X^{-1}(1-\varepsilon+\varepsilon U_X)$,
--   $$\mathop{\boxplus}_{i=1}^n\rho_i(X)=\mathop{\boxplus}_{i=1}^n\rho_i^*(X_\varepsilon);$$
--   2. the constrained inf-convolution $\boxplus_{i=1}^n\rho_i$ is an $\varepsilon$-tail risk measure: $\boxplus_{i=1}^n\rho_i(X)=\boxplus_{i=1}^n\rho_i(Y)$ whenever $X_\varepsilon\overset{d}{=}Y_\varepsilon$.
--
--   When risk sharing is restricted to comonotonic allocations, the tail parameter of the aggregate is the maximum of the individual tail parameters, in contrast with the sum obtained for the unconstrained inf-convolution (Theorem 3 of the paper).
--
--   **Formalization Note** $\boxplus$ is valued in extended reals. The generators are hypotheses, as in the statement of the theorem; their existence is Proposition 3.1 of Liu and Wang (2021), cited and not formalized. The maximum $\varepsilon$ is written as the supremum $\sup_j\varepsilon_j$ over the finite nonempty index set. Equality in law of tails is encoded through (6). Part (iii) of the theorem (convex-order consistent measures) is not part of this statement.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), pp. 20–21, Theorem 4 (i)–(ii); proof p. 21

import Mathlib
import Definitions.Def_TailRiskSharing_ComonoConv_Setting
import Definitions.Def_TailRiskSharing_ComonoConv_Comonotone

namespace TailRiskSharing.ComonoConv

open MeasureTheory

theorem theorem4_comonotonic_inf_convolution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (n : ℕ) (hn : 1 ≤ n) (ρ ρstar : Fin n → (Ω → ℝ) → ℝ) (εs : Fin n → ℝ)
    (hε : ∀ i, 0 < εs i ∧ εs i < 1)
    (htail : ∀ i, IsTailRiskMeasure P L0 (εs i) (ρ i))
    (hgen : ∀ i, IsGenerator P L0 (⨆ j, εs j) (ρ i) (ρstar i)) :
    (∀ X ∈ L0, ∀ U : Ω → ℝ, IsQuantileUniform P X U →
        comonoInfConv P L0 ρ X = comonoInfConv P L0 ρstar (tailRV P (⨆ j, εs j) X U)) ∧
      TailRiskSharing.VaRTail.IsTailRiskMeasureE P L0 (⨆ j, εs j) (comonoInfConv P L0 ρ) := by sorry

end TailRiskSharing.ComonoConv
