-- Prove2me | Theorems.Thm_TailRiskSharing_TailConv_embrechts_cor1_varL_sum
-- name    : TailRiskSharing.TailConv.embrechts_cor1_varL_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:42.12946+00:00
-- url     : https://prove2.me/theorems/82512423-e141-4fe3-8adb-28e352d79f15
-- title:
--   p. 17 (Corollary 1 of Embrechts et al. 2018, as used) — Σ VaR^L_{εᵢ}(Xᵢ) ≥ VaR^L_{Σεᵢ}(Σ Xᵢ)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be an atomless probability space, $n\ge1$, $X_1,\dots,X_n\in L^\infty$, and $\varepsilon_1,\dots,\varepsilon_n\in(0,1)$ with $\sum_{i=1}^n\varepsilon_i<1$. Then
--   $$\sum_{i=1}^n \mathrm{VaR}^L_{\varepsilon_i}(X_i)\ \ge\ \mathrm{VaR}^L_{\sum_{i=1}^n\varepsilon_i}\Bigl(\sum_{i=1}^n X_i\Bigr).$$
--
--   In the proof of Theorem 3 this is the inequality $x_1+\dots+x_n\ge x$ with $x_i=\mathrm{VaR}^L_{\varepsilon_i}(X_i)$ and $x=\mathrm{VaR}^L_\varepsilon(X)$ for $X=\sum_i X_i$, deduced there from Corollary 1 of Embrechts, Liu and Wang (2018). It shows that the left VaRs of the parts dominate the left VaR of the total at the summed level.
--
--   **Formalization Note** Only the case $\sum_i\varepsilon_i<1$ is stated. When $\sum_i\varepsilon_i\ge1$ the proof takes $\varepsilon=1$ and $x=-\infty$, where the inequality is trivial.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 17, proof of Theorem 3 (Corollary 1 of Embrechts et al. (2018), as used)

import Mathlib
import Definitions.Def_TailRiskSharing_TailConv_Setting

open MeasureTheory

namespace TailRiskSharing.TailConv

/-- Corollary 1 of Embrechts et al. (2018), as used in the proof of Theorem 3, p. 17:
`x_1 + ⋯ + x_n ≥ x` with `x_i = VaR^L_{ε_i}(X_i)` and `x = VaR^L_{Σ ε_i}(Σ X_i)`, for
`ε_i ∈ (0,1)` with `Σ ε_i < 1`. -/
theorem embrechts_cor1_varL_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P) (n : ℕ) (hn : 1 ≤ n) (εs : Fin n → ℝ)
    (hε : ∀ i, 0 < εs i ∧ εs i < 1) (hsum : ∑ i, εs i < 1) (Xs : Fin n → Ω → ℝ)
    (hXs : ∀ i, Xs i ∈ Linf P) :
    TailRiskSharing.VaRConv.VaRL P (∑ i, εs i) (fun ω => ∑ i, Xs i ω) ≤ ∑ i, TailRiskSharing.VaRConv.VaRL P (εs i) (Xs i) := by sorry

end TailRiskSharing.TailConv
