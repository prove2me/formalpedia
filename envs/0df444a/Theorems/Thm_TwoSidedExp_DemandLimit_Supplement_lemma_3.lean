-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_Supplement_lemma_3
-- name    : TwoSidedExp.DemandLimit.Supplement.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:22:46.489265+00:00
-- url     : https://prove2.me/theorems/28835b9f-ad23-4b6b-bced-f478f1f54c46
-- title:
--   Lemma 3 (supports Theorem 2) — uniform binomial L¹ concentration
-- statement:
--   Fix B > 0 and p ∈ [0,1]. At a grid point y ∈ [0,B] with Ny an integer, let X^(N)(y) have the binomial law with Ny trials and success probability p. Then
--
--   $$\sup_{0\le y\le B:\ Ny\in\mathbb Z}\mathbb E\left|\frac{X^{(N)}(y)}N-py\right|\longrightarrow0\quad(N\to\infty).$$
--
--   This is uniform L¹ concentration over all trial counts up to NB, including zero trials and p=0 or p=1.
--
--   **Formalization Note** The grid is indexed by k=Ny ∈ ℕ with k ≤ BN, so the expectation is taken directly under Mathlib's Binomial(k,p) measure. The finite set of expectations is nonempty (k=0), bounded, and its real supremum has no default-value ambiguity. N=0 is an irrelevant sequence extension.
--
--   Differences from the source:
--   - encoding: The supremum is over y in [0,B] with Ny integral. → It is the real supremum over natural trial counts k ≤ BN of the binomial expectation centered at pk/N.; reason: For every N≥1, y=k/N is a bijection of these finite nonempty grids, and only N→∞ is asserted.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. A5 (PDF 41), Lemma 3

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

/-- Lemma 3, p. A5: reindex the finite grid by its natural trial count k = Ny. -/
theorem lemma_3 (B : ℝ) (hB : 0 < B) (p : Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N : ℕ => sSup {r : ℝ | ∃ k : ℕ, (k : ℝ) ≤ B * N ∧
      r = ∫ x : ℕ, |(x : ℝ) / N - (p : ℝ) * ((k : ℝ) / N)|
        ∂(ProbabilityTheory.binomial k p)}) atTop (𝓝 0) := by sorry

end TwoSidedExp.DemandLimit.Supplement
