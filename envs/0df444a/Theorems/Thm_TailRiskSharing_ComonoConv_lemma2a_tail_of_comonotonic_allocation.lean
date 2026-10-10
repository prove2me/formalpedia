-- Prove2me | Theorems.Thm_TailRiskSharing_ComonoConv_lemma2a_tail_of_comonotonic_allocation
-- name    : TailRiskSharing.ComonoConv.lemma2a_tail_of_comonotonic_allocation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:14.748079+00:00
-- url     : https://prove2.me/theorems/428d1907-7d1a-417a-889b-c4ab39a04477
-- title:
--   Lemma 2(a), p. 21 — a comonotonic allocation of X yields one of X_ε with Yᵢ =d (Xᵢ)_ε
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $n\ge 1$, $X\in L^0$, $\varepsilon\in(0,1)$, and let $U_X$ be a quantile uniform of $X$, so that $X_\varepsilon=F_X^{-1}(1-\varepsilon+\varepsilon U_X)$.
--
--   For every comonotonic allocation $(X_1,\dots,X_n)\in\mathbb A_n^+(X)$ there exists a comonotonic allocation $(Y_1,\dots,Y_n)\in\mathbb A_n^+(X_\varepsilon)$ of the tail such that $Y_i\overset{d}{=}(X_i)_\varepsilon$ for $i=1,\dots,n$, that is,
--   $$\mathbb P(Y_i\le x)=\frac{(F_{X_i}(x)-(1-\varepsilon))_+}{\varepsilon}\qquad\text{for all }x\in\mathbb R,\ i=1,\dots,n.$$
--
--   Together with part (b), this lemma matches comonotonic allocations of a risk with comonotonic allocations of its tail, which is the core of the proof of Theorem 4.
--
--   **Formalization Note** The law of $(X_i)_\varepsilon$ is written through (6), so no quantile uniform of $X_i$ has to be chosen. The hypothesis $n\ge 1$ (at least one agent) is the paper's implicit convention.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 21, Lemma 2(a); proof p. 38, App. B

import Mathlib
import Definitions.Def_TailRiskSharing_ComonoConv_Setting
import Definitions.Def_TailRiskSharing_ComonoConv_Comonotone

namespace TailRiskSharing.ComonoConv

open MeasureTheory

theorem lemma2a_tail_of_comonotonic_allocation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (n : ℕ) (hn : 1 ≤ n) (X : Ω → ℝ) (hX : X ∈ L0) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (U : Ω → ℝ) (hU : IsQuantileUniform P X U)
    (Xs : Fin n → Ω → ℝ) (hXs : Xs ∈ ComonoAllocations P L0 n X) :
    ∃ Ys ∈ ComonoAllocations P L0 n (tailRV P ε X U),
      ∀ i, ∀ x : ℝ, distFn P (Ys i) x = max (distFn P (Xs i) x - (1 - ε)) 0 / ε := by sorry

end TailRiskSharing.ComonoConv
