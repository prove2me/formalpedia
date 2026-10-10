-- Prove2me | Theorems.Thm_TailRiskSharing_ComonoConv_lemma2b_comonotonic_allocation_of_tail
-- name    : TailRiskSharing.ComonoConv.lemma2b_comonotonic_allocation_of_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:46.227983+00:00
-- url     : https://prove2.me/theorems/e4299ec4-9a0a-4880-9811-dea0c7fccfd7
-- title:
--   Lemma 2(b), p. 21 — a comonotonic allocation of X_ε lifts to one of X with (Xᵢ)_ε =d Yᵢ
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $n\ge 1$, $X\in L^0$, $\varepsilon\in(0,1)$, and let $U_X$ be a quantile uniform of $X$, so that $X_\varepsilon=F_X^{-1}(1-\varepsilon+\varepsilon U_X)$.
--
--   For every comonotonic allocation $(Y_1,\dots,Y_n)\in\mathbb A_n^+(X_\varepsilon)$ of the tail there exists a comonotonic allocation $(X_1,\dots,X_n)\in\mathbb A_n^+(X)$ such that $(X_i)_\varepsilon\overset{d}{=}Y_i$ for $i=1,\dots,n$, that is,
--   $$\frac{(F_{X_i}(x)-(1-\varepsilon))_+}{\varepsilon}=\mathbb P(Y_i\le x)\qquad\text{for all }x\in\mathbb R,\ i=1,\dots,n.$$
--
--   This is the converse direction to part (a); together they show that the comonotonic risk sharing of $X$ and of its tail $X_\varepsilon$ have the same tail-level outcomes.
--
--   **Formalization Note** The law of $(X_i)_\varepsilon$ is written through (6). The hypothesis $n\ge 1$ is needed: with no agents, $\mathbb A_0^+(X_\varepsilon)$ is nonempty when $X_\varepsilon=0$, while $\mathbb A_0^+(X)$ is empty unless $X=0$.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 21, Lemma 2(b); proof p. 38, App. B

import Mathlib
import Definitions.Def_TailRiskSharing_ComonoConv_Setting
import Definitions.Def_TailRiskSharing_ComonoConv_Comonotone

namespace TailRiskSharing.ComonoConv

open MeasureTheory

theorem lemma2b_comonotonic_allocation_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (n : ℕ) (hn : 1 ≤ n) (X : Ω → ℝ) (hX : X ∈ L0) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (U : Ω → ℝ) (hU : IsQuantileUniform P X U)
    (Ys : Fin n → Ω → ℝ) (hYs : Ys ∈ ComonoAllocations P L0 n (tailRV P ε X U)) :
    ∃ Xs ∈ ComonoAllocations P L0 n X,
      ∀ i, ∀ x : ℝ, max (distFn P (Xs i) x - (1 - ε)) 0 / ε = distFn P (Ys i) x := by sorry

end TailRiskSharing.ComonoConv
