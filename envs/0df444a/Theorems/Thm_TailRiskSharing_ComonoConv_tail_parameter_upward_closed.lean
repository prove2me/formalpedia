-- Prove2me | Theorems.Thm_TailRiskSharing_ComonoConv_tail_parameter_upward_closed
-- name    : TailRiskSharing.ComonoConv.tail_parameter_upward_closed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:53.410129+00:00
-- url     : https://prove2.me/theorems/f2db246a-66ca-478d-addf-c34ade198b84
-- title:
--   p. 8 — every q ∈ [p, 1) is a tail parameter of a p-tail risk measure
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and let $\rho$ be a risk measure on $L^0$. Let $0<p\le q<1$. If $\rho$ is a $p$-tail risk measure, that is, $\rho(X)=\rho(Y)$ whenever $X_p\overset{d}{=}Y_p$, then $\rho$ is also a $q$-tail risk measure:
--   $$X_q\overset{d}{=}Y_q\ \Longrightarrow\ \rho(X)=\rho(Y)\qquad (X,Y\in L^0).$$
--
--   Thus the notion of a $p$-tail risk measure becomes weaker as $p$ increases. In the proof of Theorem 4 this is what allows every $\varepsilon_i$-tail risk measure to be treated as an $\varepsilon$-tail risk measure for $\varepsilon=\bigvee_i\varepsilon_i$.
--
--   **Formalization Note** Equality in law of tails is encoded through (6): $X_p\overset{d}{=}Y_p$ means $(F_X(x)-(1-p))_+=(F_Y(x)-(1-p))_+$ for all $x$.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 8, §2.4, sentence after Definition 1; used in the proof of Theorem 4, p. 21

import Mathlib
import Definitions.Def_TailRiskSharing_ComonoConv_Setting
import Definitions.Def_TailRiskSharing_ComonoConv_Comonotone

namespace TailRiskSharing.ComonoConv

open MeasureTheory

theorem tail_parameter_upward_closed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (ρ : (Ω → ℝ) → ℝ) (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1)
    (hρ : IsTailRiskMeasure P L0 p ρ) :
    IsTailRiskMeasure P L0 q ρ := by sorry

end TailRiskSharing.ComonoConv
