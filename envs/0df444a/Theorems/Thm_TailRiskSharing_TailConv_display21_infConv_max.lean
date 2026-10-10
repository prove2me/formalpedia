-- Prove2me | Theorems.Thm_TailRiskSharing_TailConv_display21_infConv_max
-- name    : TailRiskSharing.TailConv.display21_infConv_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:47.562764+00:00
-- url     : https://prove2.me/theorems/5d2bac49-b2d8-4b32-9c88-79f9009d7b1f
-- title:
--   (21), p. 18 — □ρᵢ(X) = □ρᵢ(X′) with X′ = max{X, VaR^L_ε(X)}, ε = Σεᵢ < 1
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be an atomless probability space and $n\ge1$. For $i=1,\dots,n$ let $\rho_i:L^\infty\to\mathbb R$ be an $\varepsilon_i$-tail risk measure with $\varepsilon_i\in(0,1)$, and suppose one of them, $\rho_j$, is monotone and (sup-norm) continuous from above. Assume $\varepsilon=\sum_{i=1}^n\varepsilon_i<1$. Then for every $X\in L^\infty$,
--   $$\mathop{\square}_{i=1}^n\rho_i(X)=\mathop{\square}_{i=1}^n\rho_i(X'),\qquad X'=\max\{X,\mathrm{VaR}^L_\varepsilon(X)\}. \tag{21}$$
--
--   Identity (21) reduces the inf-convolution at $X$ to its value at a position whose distribution below the $(1-\varepsilon)$-quantile has been flattened. Together with law-invariance it yields the $\varepsilon$-tail property in Theorem 3.
--
--   **Formalization Note** For $\sum_i\varepsilon_i\ge1$ the paper has $\varepsilon=1$, $\mathrm{VaR}^L_1(X)=-\infty$ and $X'=X$, so (21) is trivial there; only $\sum_i\varepsilon_i<1$ is stated. The hypotheses are exactly those of Theorem 3.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 18, display (21) in the proof of Theorem 3

import Mathlib
import Definitions.Def_TailRiskSharing_TailConv_Setting

open MeasureTheory

namespace TailRiskSharing.TailConv

/-- (21), p. 18: under the hypotheses of Theorem 3 and `ε = Σ ε_i < 1`,
`□ρ_i(X) = □ρ_i(X')` with `X' = max{X, VaR^L_ε(X)}`, for every `X ∈ L^∞`. -/
theorem display21_infConv_max {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P) (n : ℕ) (hn : 1 ≤ n)
    (ρ : Fin n → (Ω → ℝ) → ℝ) (εs : Fin n → ℝ) (hε : ∀ i, 0 < εs i ∧ εs i < 1)
    (htail : ∀ i, TailRiskSharing.VaRTail.IsTailRiskMeasure P (Linf P) (εs i) (ρ i))
    (j : Fin n) (hmono : TailRiskSharing.VaRTail.IsMonotone P (Linf P) (ρ j))
    (hcont : IsSupNormContinuousFromAbove P (Linf P) (ρ j))
    (hsum : ∑ i, εs i < 1) (X : Ω → ℝ) (hX : X ∈ Linf P) :
    TailRiskSharing.VaRConv.infConv (Linf P) ρ X =
      TailRiskSharing.VaRConv.infConv (Linf P) ρ (fun ω => max (X ω) (TailRiskSharing.VaRConv.VaRL P (∑ i, εs i) X)) := by sorry

end TailRiskSharing.TailConv
