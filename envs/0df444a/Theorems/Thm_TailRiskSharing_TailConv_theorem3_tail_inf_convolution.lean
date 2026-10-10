-- Prove2me | Theorems.Thm_TailRiskSharing_TailConv_theorem3_tail_inf_convolution
-- name    : TailRiskSharing.TailConv.theorem3_tail_inf_convolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:25.69059+00:00
-- url     : https://prove2.me/theorems/722ff83c-2240-461f-a906-b15e2be62562
-- title:
--   Theorem 3, p. 17 — □ρᵢ of εᵢ-tail risk measures is a monotone min{Σεᵢ, 1}-tail risk measure
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be an atomless probability space and $n\ge1$. For $i=1,\dots,n$ let $\rho_i:L^\infty\to\mathbb R$ be an $\varepsilon_i$-tail risk measure for some $\varepsilon_i\in(0,1)$. If one of $\rho_1,\dots,\rho_n$ is monotone and (sup-norm) continuous from above, then
--   $$\mathop{\square}_{i=1}^n\rho_i\ \text{ is a monotone }\varepsilon\text{-tail risk measure},\qquad \varepsilon=\min\Bigl\{\sum_{i=1}^n\varepsilon_i,\,1\Bigr\}.$$
--   Here a $1$-tail risk measure means a law-invariant one.
--
--   Sharing risk among agents whose risk measures only look at the tails produces an aggregate risk measure that again only looks at a tail, of probability at most the sum of the individual tail probabilities. The parameter is sharp: for right VaRs, $\mathop{\square}_i\mathrm{VaR}^R_{\alpha_i}=\mathrm{VaR}^R_{\sum_i\alpha_i}$, whose smallest tail parameter is $\sum_i\alpha_i$.
--
--   **Formalization Note** The domain is $L^\infty$, a disclosed specialization of the paper's general domain $\mathcal X$. The $\rho_i$ are real-valued; the inf-convolution takes values in $[-\infty,\infty]$ (`EReal`) and both properties are stated for it without assuming finiteness. The tail property at level $\varepsilon$ is encoded through display (6); at $\varepsilon=1$ it is exactly law-invariance. "One of" is an index $j$ carrying both hypotheses.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 17, Theorem 3; proof pp. 17–18

import Mathlib
import Definitions.Def_TailRiskSharing_TailConv_Setting

open MeasureTheory

namespace TailRiskSharing.TailConv

/-- Theorem 3, p. 17: if `ρ_i` is an `ε_i`-tail risk measure, `ε_i ∈ (0,1)`, `i = 1, …, n`,
and one of `ρ_1, …, ρ_n` is monotone and (sup-norm) continuous from above, then
`□_{i=1}^n ρ_i` is a monotone `ε`-tail risk measure with `ε = min{Σ ε_i, 1}`
(on `L^∞` over an atomless probability space). -/
theorem theorem3_tail_inf_convolution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P) (n : ℕ) (hn : 1 ≤ n)
    (ρ : Fin n → (Ω → ℝ) → ℝ) (εs : Fin n → ℝ) (hε : ∀ i, 0 < εs i ∧ εs i < 1)
    (htail : ∀ i, TailRiskSharing.VaRTail.IsTailRiskMeasure P (Linf P) (εs i) (ρ i))
    (j : Fin n) (hmono : TailRiskSharing.VaRTail.IsMonotone P (Linf P) (ρ j))
    (hcont : IsSupNormContinuousFromAbove P (Linf P) (ρ j)) :
    TailRiskSharing.VaRTail.IsMonotoneE P (Linf P) (TailRiskSharing.VaRConv.infConv (Linf P) ρ) ∧
      TailRiskSharing.VaRTail.IsTailRiskMeasureE P (Linf P) (min (∑ i, εs i) 1) (TailRiskSharing.VaRConv.infConv (Linf P) ρ) := by sorry

end TailRiskSharing.TailConv
