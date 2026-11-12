-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_lemma_8
-- name    : PQNormIPM1352.Main.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:32.967202+00:00
-- url     : https://prove2.me/theorems/707b76ff-5a4c-43eb-b1da-11c9b7e50300
-- title:
--   Lemma 8 — with $\eta_0=\sqrt2/(10\sqrt s)$, $\lambda_{\eta_0}(x_0)\le 1/10$
-- statement:
--   Let $p \ge q > 1$, let the support $S$ ($s$ entries) have no all-zero row or column, and let the non-zero entries satisfy $0 < A(i,j) \le 1$ (the normalization $\max_S A(i,j) \le 1$ of §4.1). Let $x_0$ be the analytic center of Lemma 7, $c = -\bar a$ with $\bar a = (0,0,a)$, and
--   $$\eta_0 = \frac{\sqrt2}{10\sqrt s}.$$
--   Then the Newton decrement of $\Phi_{\eta_0}(x) = F(x) + \eta_0\langle c, x\rangle$ at $x_0$ satisfies
--   $$\lambda_{\eta_0}(x_0) \le \frac1{10}.$$
--
--   This puts the starting point of Algorithm 1 in the quadratic-convergence region required by Theorem 12.
--
--   Differences from the source:
--   - encoding: the non-negative matrix after removing all-zero rows and columns, a standing assumption of §3 (p. 7) → a sparsity pattern with every row and column occupied (`Preprocessed`) and the barrier on ℝ^{m+n+s}; reason: the paper removes such rows and columns before (5) and works with the support S only
--   - encoding: non-negative A with max_{(i,j)∈S} A(i,j) ≤ 1 (§4.1, p. 9) → entry values 0 < a_k ≤ 1; reason: the entries on S are the non-zero (hence positive) entries of A; the bound is the section's standing normalization
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Lemma 8, printed p. 10 (PDF p. 11); standing assumption max_S A(i,j) ≤ 1, §4.1, p. 9

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_Barrier

namespace PQNormIPM1352.Main

/-- **Lemma 8** (Pirazzini–Spielman, STOC 2027 #1352, p. 10; standing assumption of §4.1, p. 9:
`max_S A(i,j) ≤ 1`). For `p ≥ q > 1`, a preprocessed pattern with entries `0 < a_k ≤ 1`, `x₀` as in
Lemma 7 and `η₀ = √2 / (10 √s)`, the Newton decrement of `Φ_{η₀} = F + η₀ ⟨−ā, ·⟩` at `x₀` is at
most `1/10`. -/
theorem lemma_8 {m n s : ℕ} (P : SparsePattern m n s) (hP : P.Preprocessed) (p q : ℝ)
    (hq : 1 < q) (hqp : q ≤ p) (a : Fin s → ℝ) (ha : ∀ k, 0 < a k ∧ a k ≤ 1) :
    newtonDecrement (penalized (P.barrierF p q) (P.cvec a) (eta0 s)) (P.initPoint p q) ≤ 1 / 10 := by sorry

end PQNormIPM1352.Main
