-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_6_8
-- name    : SKHessianAscent.lemma_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:20:37.493933+00:00
-- url     : https://prove2.me/theorems/ac9419e7-a612-43ac-81ba-f58151702c19
-- title:
--   Lemma 6.8 — short paths preserving the spectral gap: a path in $S_D$ of $L^2$-length at most $\frac{2}{1-\beta^2}\|W_1-W_0\|_{L^2}$
-- statement:
--   Fix $0<\beta<1$, $c>0$ and a symmetric $A\in\mathbb R^{n\times n}$. Let $S_D=\{D\in\mathcal D_n([1,\infty)):\beta^2\mathrm{tr}_n(D^{-1})I_n-\beta A+D\succeq cI_n\}$, and let $W_0,W_1$ be diagonal matrices with entries in $(0,1]$ such that $W_0^{-1},W_1^{-1}\in S_D$. Then there is a piecewise $C^1$ path $W:[0,1]\to\mathcal D_n((0,1])$ with $W(0)=W_0$, $W(1)=W_1$,
--
--   $$
--   W(t)^{-1}\in S_D\quad(0\le t\le1),\qquad\int_0^1\|W'(t)\|_{L^2}\,dt\le\frac{2}{1-\beta^2}\,\|W_1-W_0\|_{L^2},
--   $$
--
--   where $\|X\|_{L^2}=\|X\|_F/\sqrt n$.
--
--   The set of admissible $W$ is not convex, so a segment from $W_0$ to $W_1$ may leave it; the lemma supplies a path inside it whose length is comparable to the distance of the endpoints, along which derivative bounds can be integrated (Lemma 6.9).
--
--   **Formalization Note** Diagonal matrices are their diagonal vectors. "Piecewise $C^1$" is encoded as: continuous on $[0,1]$, and, outside a finite set of times, differentiable with a derivative that is continuous and bounded; the length is the integral of $\|W'(t)\|_{L^2}$, which under these conditions is the length of the path.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma 6.8, eqs. (6.15)–(6.16), pp. 39–40; (6.4), p. 37

import Mathlib
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Resolvent

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem lemma_6_8 (β c : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (w₀ w₁ : Fin n → ℝ)
    (h₀ : ∀ i, 0 < w₀ i ∧ w₀ i ≤ 1) (h₁ : ∀ i, 0 < w₁ i ∧ w₁ i ≤ 1)
    (hS₀ : (fun i => (w₀ i)⁻¹) ∈ SD β A c) (hS₁ : (fun i => (w₁ i)⁻¹) ∈ SD β A c) :
    ∃ (W : ℝ → Fin n → ℝ) (s : Finset ℝ) (B : ℝ),
      ContinuousOn W (Set.Icc 0 1) ∧ W 0 = w₀ ∧ W 1 = w₁ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ s →
        DifferentiableAt ℝ W t ∧ ∀ i, |deriv W t i| ≤ B) ∧
      ContinuousOn (deriv W) (Set.Icc 0 1 \ (s : Set ℝ)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∀ i, 0 < W t i ∧ W t i ≤ 1) ∧ (fun i => (W t i)⁻¹) ∈ SD β A c) ∧
      ∫ t in (0 : ℝ)..1, Real.sqrt ((∑ i, deriv W t i ^ 2) / n) ≤
        2 / (1 - β ^ 2) * Real.sqrt ((∑ i, (w₁ i - w₀ i) ^ 2) / n) := by sorry

end SKHessianAscent
