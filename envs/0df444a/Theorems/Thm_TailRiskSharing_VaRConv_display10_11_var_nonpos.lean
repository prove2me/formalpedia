-- Prove2me | Theorems.Thm_TailRiskSharing_VaRConv_display10_11_var_nonpos
-- name    : TailRiskSharing.VaRConv.display10_11_var_nonpos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:21:40.845119+00:00
-- url     : https://prove2.me/theorems/b2ee29c4-f37b-4998-ba9f-ab0ccc7a2f66
-- title:
--   (10)–(11), p. 9 — VaR^R_β(Y) ≤ 0 iff P(Y > ε) < β ∀ε > 0, and VaR^L_β(Y) ≤ 0 iff P(Y > 0) ≤ β
-- statement:
--   Let $\mathbb P$ be a probability measure, $Y$ a random variable and $\beta\in(0,1)$. Then
--
--   $$\mathrm{VaR}^R_\beta(Y)\le 0\iff \mathbb P(Y>\varepsilon)<\beta\ \text{ for all }\varepsilon>0,$$
--
--   and
--
--   $$\mathrm{VaR}^L_\beta(Y)\le 0\iff \mathbb P(Y>0)\le\beta.$$
--
--   These two characterizations of a non-positive quantile are the basic tool of the proof of Theorem 1: they turn bounds on VaRs of shares of a risk into bounds on tail probabilities.
--
--   **Formalization Note** $Y$ is measurable ($Y\in L^0$). Atomlessness is not assumed: the equivalences hold under any probability measure.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 9, proof of Theorem 1, displays (10) and (11)

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

open MeasureTheory ProbabilityTheory

namespace TailRiskSharing.VaRConv

theorem display10_11_var_nonpos {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Y ∈ (L0 : Set (Ω → ℝ))) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (VaRR P β Y ≤ 0 ↔ ∀ ε : ℝ, 0 < ε → P.real {ω | ε < Y ω} < β) ∧
    (VaRL P β Y ≤ 0 ↔ P.real {ω | 0 < Y ω} ≤ β) := by sorry

end TailRiskSharing.VaRConv
