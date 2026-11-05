-- Prove2me | Theorems.Thm_TailRiskSharing_VaRTail_exists_quantile_uniform
-- name    : TailRiskSharing.VaRTail.exists_quantile_uniform
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T04:44:09.117889+00:00
-- url     : https://prove2.me/theorems/e2a9d314-ebf0-473c-8da8-ec6b8594972f
-- title:
--   §2.1, p. 5 — existence of $U_X$ uniform on $[0,1]$ with $F_X^{-1}(U_X)=X$ a.s. on an atomless space
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space (every measurable set $A$ with $\mathbb P(A)>0$ contains a measurable $B\subseteq A$ with $0<\mathbb P(B)<\mathbb P(A)$). Then for every random variable $X\in L^0$ there exists a random variable $U_X$, uniformly distributed on $[0,1]$, such that
--   $$F_X^{-1}(U_X)=X\quad\text{a.s.},$$
--   where $F_X^{-1}(p)=\inf\{x\in\mathbb R: F_X(x)\ge p\}$ is the left-continuous quantile function of $X$.
--
--   In the formalization, "uniform on $[0,1]$" means $U$ is measurable with law $\mathbb P\circ U^{-1}=\mathrm{Leb}|_{[0,1]}$, and $F_X^{-1}(p)$ is expressed as $\mathrm{VaR}^L_{1-p}(X)$ (the predicate `IsQuantileUniform`). This is the existence statement that §2.1 of the paper invokes for every $X$ and that Theorem 2 (iv) relies on to compare $X^{[\alpha-\delta]}$ across tail-equivalent random variables.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), §2.1 p. 5 (existence of U_X, citing Föllmer & Schied, Stochastic Finance, 4th ed. 2016, Lemma A.32)

import Mathlib
import Definitions.Def_TailRiskSharing_VaRTail_Setting

open MeasureTheory

namespace TailRiskSharing.VaRTail

theorem exists_quantile_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (X : Ω → ℝ) (hX : X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ))) :
    ∃ U : Ω → ℝ, IsQuantileUniform P X U := by sorry

end TailRiskSharing.VaRTail
