-- Prove2me | Theorems.Thm_UniversalSubmod_lemma_2_5
-- name    : UniversalSubmod.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:51:33.13188+00:00
-- url     : https://prove2.me/theorems/3846c259-c28c-471e-83ba-284d8066d0c1
-- title:
--   Lemma 2.5 — $n$ unit vectors in $\mathbb R^k$, $k\ge 4\varepsilon^{-2}\ln n$, with $|\langle v_i,v_j\rangle|\le\varepsilon$
-- statement:
--   Let $n\ge1$ be an integer, let $\varepsilon>0$, and let $k$ be a positive integer with
--   $$
--   k\ \ge\ \frac{4}{\varepsilon^2}\,\ln n .
--   $$
--   Then there exist vectors $v_1,\dots,v_n\in\mathbb R^k$ such that $\|v_i\|=1$ for every $i$ and
--   $$
--   |\langle v_i,v_j\rangle|\le\varepsilon\qquad\text{for all } i\ne j .
--   $$
--
--   So $n$ nearly orthogonal unit vectors fit in dimension $O(\varepsilon^{-2}\log n)$. This logarithmic dimension is what makes the discretized family of threshold sets polynomially large in the proof of Theorem 1.1.
--
--   **Formalization Note** $\mathbb R^k$ is `EuclideanSpace ℝ (Fin k)`; $\ln$ is `Real.log` of the real number $n$.
--
--   Differences from the source:
--   - encoding: vectors $v_1,\dots,v_n\in\mathbb R^k$ → a map `Fin n → EuclideanSpace ℝ (Fin k)`; reason: a relabelling of $[n]$ and the same space
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), Lemma 2.5, p.7 (proof p.11)

import Mathlib

namespace UniversalSubmod

open scoped RealInnerProductSpace

/-- **Lemma 2.5** (near-orthogonal unit vectors; Adamczyk, Ueltzen, Vondrák, *Optimal universal
sets for submodular functions*, manuscript of November 3, 2026, Lemma 2.5, p.7; proof p.11).
Let `n ≥ 1` be an integer, `ε > 0` and let `k ≥ (4/ε²) ln n` be a positive integer. Then there
exist vectors `v₁, …, vₙ ∈ ℝ^k` with `‖vᵢ‖ = 1` and `|⟨vᵢ, vⱼ⟩| ≤ ε` for `i ≠ j`.

**Formalization Note.** `ℝ^k` is `EuclideanSpace ℝ (Fin k)`; the vectors are indexed by `Fin n`;
`ln` is `Real.log` of the real number `n ≥ 1`. -/
theorem lemma_2_5 (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 0 < k)
    (hkn : 4 / ε ^ 2 * Real.log n ≤ (k : ℝ)) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin k),
      (∀ i, ‖v i‖ = 1) ∧ ∀ i j, i ≠ j → |⟪v i, v j⟫| ≤ ε := by sorry

end UniversalSubmod
