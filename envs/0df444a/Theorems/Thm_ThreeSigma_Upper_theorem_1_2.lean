-- Prove2me | Theorems.Thm_ThreeSigma_Upper_theorem_1_2
-- name    : ThreeSigma.Upper.theorem_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:16.32009+00:00
-- url     : https://prove2.me/theorems/85467f20-e797-465b-b45f-eee6895dc8a5
-- title:
--   Theorem 1.2 — three standard deviations suffice, including the square case
-- statement:
--   For every $n,d\in\mathbb N$ and every real matrix $A\in[-1,1]^{d\times n}$, there is a sign vector $x\in\{-1,1\}^n$ such that
--   $$\|Ax\|_\infty\le\sqrt{3n\operatorname{arsinh}(10d/n)}+4.$$
--   For every $n\ge1$ and every square $A\in[-1,1]^{n\times n}$ there is a sign vector satisfying
--   $$\|Ax\|_\infty\le\left(\sqrt{3\operatorname{arsinh}(10)}+\frac4{\sqrt n}\right)\sqrt n.$$
--   Equivalently, the source's maximum normalized discrepancy obeys $D_n\le\sqrt{3\operatorname{arsinh}(10)}+4/\sqrt n$. The coefficient itself satisfies
--   $$\sqrt{3\operatorname{arsinh}(10)}+\frac4{\sqrt n}<3\qquad(n\ge10^8).$$
--   The theorem retains arbitrary rectangular matrices, the exact constant, and the complete numerical consequence in the square case.
--
--   Differences from the source:
--   - encoding: matrix infinity-norm bounds → an absolute-value inequality for every row, with coordinates indexed by Fin; reason: the bound is nonnegative and a finite supremum is bounded exactly when every coordinate is bounded; with no rows the norm is zero
--   - encoding: D_n is the maximum of disc(A)/√n over square bounded matrices → for every square bounded matrix there exists a signing with discrepancy at most the displayed coefficient times √n, for n≥1; reason: for positive n this is exactly the maximum/minimum claim, since the set of signings is finite and nonempty; n=0 has no defined normalization in the source
--   - encoding: the first clause quantifies all natural n but writes 10d/n → at n=0 total division gives 10d/0=0 and bound 4; reason: the empty signing has zero row sums; no positive-dimensional instance changes
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), Theorem 1.2, p. 2, restated as Theorem 3.1, p. 5; proof p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf

import Mathlib

namespace ThreeSigma.Upper

/-- Theorem 1.2, including both parts of its "In particular" clause.
At n = 0 total division gives bound 4 and all row sums are zero. -/
theorem theorem_1_2 :
    (∀ (n d : ℕ) (A : Fin d → Fin n → ℝ), (∀ i j, |A i j| ≤ 1) →
      ∃ x : Fin n → ℝ, (∀ j, x j = 1 ∨ x j = -1) ∧
        ∀ i, |∑ j, A i j * x j| ≤
          Real.sqrt (3 * (n : ℝ) * Real.arsinh (10 * (d : ℝ) / (n : ℝ))) + 4) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ A : Fin n → Fin n → ℝ,
      (∀ i j, |A i j| ≤ 1) →
      ∃ x : Fin n → ℝ, (∀ j, x j = 1 ∨ x j = -1) ∧
        ∀ i, |∑ j, A i j * x j| ≤
          (Real.sqrt (3 * Real.arsinh 10) + 4 / Real.sqrt (n : ℝ)) *
            Real.sqrt (n : ℝ)) ∧
    (∀ (n : ℕ), 10 ^ 8 ≤ n →
      Real.sqrt (3 * Real.arsinh 10) + 4 / Real.sqrt (n : ℝ) < 3) := by sorry

end ThreeSigma.Upper
