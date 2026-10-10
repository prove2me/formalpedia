-- Prove2me | Theorems.Thm_TailRiskSharing_TailConv_infConv_monotone
-- name    : TailRiskSharing.TailConv.infConv_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:23.571982+00:00
-- url     : https://prove2.me/theorems/03fbb07c-7553-4b08-b01e-386b820fa874
-- title:
--   p. 18 (Lemma 1 of Liu et al. 2020, as used) — □ρᵢ is monotone if one ρⱼ is monotone
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be an atomless probability space, $n\ge1$, and $\rho_1,\dots,\rho_n:L^\infty\to\mathbb R$. If one of them, $\rho_j$, is monotone, then the inf-convolution
--   $$\mathop{\square}_{i=1}^n\rho_i:L^\infty\to[-\infty,\infty)$$
--   is monotone: $\mathop{\square}_{i=1}^n\rho_i(X)\le\mathop{\square}_{i=1}^n\rho_i(Y)$ for all $X,Y\in L^\infty$ with $X\le Y$ a.s.
--
--   The proof of Theorem 3 uses this twice, citing Lemma 1 of Liu, Wang and Wei (2020). No other ρᵢ needs any property.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 18, proof of Theorem 3 (Lemma 1 of Liu et al. (2020), as used)

import Mathlib
import Definitions.Def_TailRiskSharing_TailConv_Setting

open MeasureTheory

namespace TailRiskSharing.TailConv

/-- p. 18 (Lemma 1 of Liu et al. (2020), as used): as long as one of `ρ_1, …, ρ_n` is
monotone, `□_{i=1}^n ρ_i` is monotone (on `L^∞`). -/
theorem infConv_monotone {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P) (n : ℕ) (hn : 1 ≤ n)
    (ρ : Fin n → (Ω → ℝ) → ℝ) (j : Fin n) (hmono : TailRiskSharing.VaRTail.IsMonotone P (Linf P) (ρ j)) :
    TailRiskSharing.VaRTail.IsMonotoneE P (Linf P) (TailRiskSharing.VaRConv.infConv (Linf P) ρ) := by sorry

end TailRiskSharing.TailConv
