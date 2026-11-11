-- Prove2me | Theorems.Thm_PermInvCC_lemma_4_2
-- name    : PermInvCC.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:23:06.094926+00:00
-- url     : https://prove2.me/theorems/12a68055-f77d-4f34-b59c-d8ba63604920
-- title:
--   Lemma 4.2 — degree needed to separate adjacent integers
-- statement:
--   Let $a,b$ be nonnegative integers. Suppose a real polynomial $F$ satisfies $|F(j)|\le M$ for all integers $-a\le j\le b+1$, and $|F(1)-F(0)|\ge\Delta>0$. Then
--   $$\deg F\ge c_{M/\Delta}\sqrt{(a+1)(b+1)},$$
--   where $c_{M/\Delta}>0$ depends only on the ratio $M/\Delta$.
--
--   Boundedness is required only at integer points; this is the degree bound at the end of the quantum lower bound.
--
--   Differences from the source:
--   - encoding: c_{M/Δ} > 0 depends only on the ratio M/Δ → for every R > 0 there is c > 0 valid whenever M ≤ RΔ; reason: taking R = M/Δ gives the exact-ratio reading, and a constant for a ratio bound works for every smaller ratio
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 4.2, p.15 (proof p.48)

import Mathlib

namespace PermInvCC

/-- **Lemma 4.2 (Degree Needed to Separate Adjacent Integers)** (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, p.15). Let `a, b` be nonnegative integers.
Suppose a real polynomial `F` satisfies `|F(j)| ≤ M` for all integers `−a ≤ j ≤ b + 1`, and
`|F(1) − F(0)| ≥ Δ > 0`. Then `deg F ≥ c_{M/Δ} √((a + 1)(b + 1))`, where `c_{M/Δ} > 0` depends
only on the ratio `M/Δ`.

**Formalization Note.** "`c_{M/Δ}` depends only on `M/Δ`" is stated as: for every bound `R > 0`
on the ratio there is `c > 0` that works for all `a, b, F, M, Δ` with `M ≤ RΔ` (taking `R = M/Δ`
recovers the exact-ratio reading). `deg` is `natDegree`. -/
theorem lemma_4_2 (R : ℝ) (hR : 0 < R) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a b : ℕ) (F : Polynomial ℝ) (M Δ : ℝ), 0 < Δ → M ≤ R * Δ →
      (∀ j : ℤ, -(a : ℤ) ≤ j → j ≤ (b : ℤ) + 1 → |F.eval (j : ℝ)| ≤ M) →
      Δ ≤ |F.eval 1 - F.eval 0| →
      c * Real.sqrt (((a : ℝ) + 1) * ((b : ℝ) + 1)) ≤ F.natDegree := by sorry

end PermInvCC
