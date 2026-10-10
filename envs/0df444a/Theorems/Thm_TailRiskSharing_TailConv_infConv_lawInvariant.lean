-- Prove2me | Theorems.Thm_TailRiskSharing_TailConv_infConv_lawInvariant
-- name    : TailRiskSharing.TailConv.infConv_lawInvariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:45.424673+00:00
-- url     : https://prove2.me/theorems/6e9e0dac-ee1a-4d16-9899-a0bf48367936
-- title:
--   p. 18 (Theorem 2 of Liu et al. 2020, as used) — □ρᵢ is law-invariant under the hypotheses of Theorem 3
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be an atomless probability space and $n\ge1$. For $i=1,\dots,n$ let $\rho_i:L^\infty\to\mathbb R$ be an $\varepsilon_i$-tail risk measure with $\varepsilon_i\in(0,1)$, and suppose one of them, $\rho_j$, is monotone and (sup-norm) continuous from above. Then the inf-convolution is law-invariant:
--   $$\mathop{\square}_{i=1}^n\rho_i(X)=\mathop{\square}_{i=1}^n\rho_i(Y)\qquad\text{for all }X,Y\in L^\infty\text{ with }X\overset{d}{=}Y.$$
--
--   Each $\rho_i$, being a tail risk measure, is law-invariant, and the paper concludes law-invariance of the inf-convolution from Theorem 2 of Liu, Wang and Wei (2020). This is the step that needs the atomless space and the continuity hypothesis.
--
--   **Formalization Note** The cited theorem is not stated in this paper; the milestone is posed with exactly the hypotheses of Theorem 3, under which the paper uses it.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 18, proof of Theorem 3 (Theorem 2 of Liu et al. (2020), as used)

import Mathlib
import Definitions.Def_TailRiskSharing_TailConv_Setting

open MeasureTheory

namespace TailRiskSharing.TailConv

/-- p. 18 (Theorem 2 of Liu et al. (2020), as used in the proof of Theorem 3): under the
hypotheses of Theorem 3, `□_{i=1}^n ρ_i` is law-invariant (on `L^∞`). -/
theorem infConv_lawInvariant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P) (n : ℕ) (hn : 1 ≤ n)
    (ρ : Fin n → (Ω → ℝ) → ℝ) (εs : Fin n → ℝ) (hε : ∀ i, 0 < εs i ∧ εs i < 1)
    (htail : ∀ i, TailRiskSharing.VaRTail.IsTailRiskMeasure P (Linf P) (εs i) (ρ i))
    (j : Fin n) (hmono : TailRiskSharing.VaRTail.IsMonotone P (Linf P) (ρ j))
    (hcont : IsSupNormContinuousFromAbove P (Linf P) (ρ j)) :
    IsLawInvariantE P (Linf P) (TailRiskSharing.VaRConv.infConv (Linf P) ρ) := by sorry

end TailRiskSharing.TailConv
