-- Prove2me | Theorems.Thm_TailRiskSharing_TailConv_lemma1_tail_max
-- name    : TailRiskSharing.TailConv.lemma1_tail_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:41.181317+00:00
-- url     : https://prove2.me/theorems/ba215222-a228-49dc-a791-ab02c0b12b41
-- title:
--   Lemma 1, p. 17 — X′_ε =d X_ε for X′ = max{X, m}, m ∈ [VaR^L_ε(X), VaR^R_ε(X)]
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be an atomless probability space, $X\in L^\infty$, and $\varepsilon\in(0,1)$. Let $m$ be any number with
--   $$\mathrm{VaR}^L_\varepsilon(X)\le m\le \mathrm{VaR}^R_\varepsilon(X),$$
--   and put $X'=\max\{X,m\}$. Then the tails of $X'$ and $X$ beyond their $(1-\varepsilon)$-quantiles have the same law:
--   $$X'_\varepsilon\overset{d}{=}X_\varepsilon .$$
--
--   Raising $X$ to a level inside its $(1-\varepsilon)$-quantile interval changes only the body of the distribution, so an $\varepsilon$-tail risk measure cannot tell $X$ and $X'$ apart. This is the technical lemma behind Theorem 3.
--
--   **Formalization Note** $X'_\varepsilon\overset{d}{=}X_\varepsilon$ is stated through display (6) as $(F_{X'}(x)-(1-\varepsilon))^+=(F_X(x)-(1-\varepsilon))^+$ for all $x$.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 17, Lemma 1; proof in Appendix B, p. 38

import Mathlib
import Definitions.Def_TailRiskSharing_TailConv_Setting

open MeasureTheory

namespace TailRiskSharing.TailConv

/-- Lemma 1, p. 17 (proof p. 38): for `X ∈ L^∞`, `ε ∈ (0,1)` and
`m ∈ [VaR^L_ε(X), VaR^R_ε(X)]`, the tails of `X' = max{X, m}` and `X` at level `ε` have the
same law: `X'_ε =d X_ε` (encoded through (6)). -/
theorem lemma1_tail_max {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (X : Ω → ℝ) (hX : X ∈ Linf P)
    (m : ℝ) (hmL : TailRiskSharing.VaRConv.VaRL P ε X ≤ m) (hmR : m ≤ TailRiskSharing.VaRConv.VaRR P ε X) :
    TailRiskSharing.VaRTail.TailEquiv P ε (fun ω => max (X ω) m) X := by sorry

end TailRiskSharing.TailConv
