-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_Supplement_lemma_2_1
-- name    : SparseLpLq.SmallP.Supplement.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:10:38.652909+00:00
-- url     : https://prove2.me/theorems/043e4ebe-ef83-4077-84d9-82697a172782
-- title:
--   Lemma 2.1 — n^{min{1/q−1/2,0}}‖x‖₂ ≤ ‖x‖_q ≤ n^{max{1/q−1/2,0}}‖x‖₂ for 1 ≤ q ≤ ∞
-- statement:
--   Let $1\le q\le\infty$, with the convention $1/\infty=0$. For every $x\in\mathbb R^n$,
--   $$n^{\min\{\frac1q-\frac12,\,0\}}\,\|x\|_2\ \le\ \|x\|_q\ \le\ n^{\max\{\frac1q-\frac12,\,0\}}\,\|x\|_2 .$$
--
--   For $q\le 2$ the left exponent is $0$ and the right one is $\frac1q-\frac12$; for $q\ge2$ the roles swap. The lemma converts between $\ell_q$ and Euclidean norms, which is how the proof of Theorem 2.1(iii) compares $\|Ax^*-b\|_q$ and $\|b\|_q$ with eigenvalue bounds.
--
--   **Formalization Note** $q$ is an extended nonnegative real with $1\le q$ ($q=\infty$ is `⊤`), and $1/q$ is `(q⁻¹).toReal`, which is $0$ at $q=\infty$. Powers of $n$ are real powers.
--
--   Differences from the source:
--   - encoding: 1 ≤ q ≤ ∞ with the convention 1/∞ = 0 (p. 3) → q : ℝ≥0∞ with 1 ≤ q; 1/q is (q⁻¹).toReal; reason: (⊤⁻¹).toReal = 0 and (q⁻¹).toReal = 1/q for finite q; same instances
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 4, Lemma 2.1

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting

open scoped ENNReal Matrix

namespace SparseLpLq.SmallP.Supplement
open SparseLpLq.SmallP
theorem lemma_2_1 {n : ℕ} (q : ℝ≥0∞) (hq : 1 ≤ q) (x : Fin n → ℝ) :
    (n : ℝ) ^ (min ((q⁻¹).toReal - 1 / 2) 0) * qNorm 2 x ≤ qNorm q x ∧
      qNorm q x ≤ (n : ℝ) ^ (max ((q⁻¹).toReal - 1 / 2) 0) * qNorm 2 x := by sorry
end SparseLpLq.SmallP.Supplement
