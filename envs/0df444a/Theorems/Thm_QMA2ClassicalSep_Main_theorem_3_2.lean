-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_theorem_3_2
-- name    : QMA2ClassicalSep.Main.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:17.864326+00:00
-- url     : https://prove2.me/theorems/fc53fcb0-4eb7-4225-87b9-3d8bdbeb37cc
-- title:
--   Theorem 3.2 — matrix Hoeffding inequality
-- statement:
--   Let $X_1,\dots,X_N$ be independent Hermitian $d\times d$ random matrices on a probability space. Suppose that for some $L>0$ and every $i$, $\mathbb EX_i=0$ and $\|X_i\|\le L$ almost surely, where $\|\cdot\|$ is the operator norm. Then for every $\eta>0$,
--
--   $$
--   \Pr\Big[\Big\|\frac1N\sum_{i=1}^NX_i\Big\|\ge\eta\Big]\le 2d\exp\Big(-\frac{N\eta^2}{8L^2}\Big).
--   $$
--
--   This is the concentration inequality ([Tro12, Theorem 1.3]) used to show that the averaged signed adjacency matrix of a NO instance is close to its conditional mean (Proposition 5.3, Lemma 6.12).
--
--   **Formalization Note** A random matrix is a measurable map into $\mathbb C^{d\times d}$ (entry functions), independence is `iIndepFun`, and the norm is Mathlib's $\ell^2$ operator norm.
--
--   Differences from the source:
--   - encoding: Hermitian d×d random matrices with operator norm → measurable maps Ω → (Fin d → Fin d → ℂ) read as matrices, iIndepFun for the product Borel structure, ℓ² operator norm; reason: Lean representation of the same objects
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 14, Theorem 3.2

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace QMA2ClassicalSep.Main

theorem theorem_3_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d N : ℕ} (X : Fin N → Ω → (Fin d → Fin d → ℂ)) (L : ℝ) (hL : 0 < L)
    (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hHerm : ∀ i ω, (Matrix.of (X i ω)).IsHermitian)
    (hMean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hBound : ∀ i, ∀ᵐ ω ∂μ, ‖Matrix.of (X i ω)‖ ≤ L) (η : ℝ) (hη : 0 < η) :
    (μ {ω | η ≤ ‖(1 / (N : ℂ)) • ∑ i, Matrix.of (X i ω)‖}).toReal ≤
      2 * d * Real.exp (-((N : ℝ) * η ^ 2) / (8 * L ^ 2)) := by sorry

end QMA2ClassicalSep.Main
