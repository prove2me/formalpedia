-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_exponentialFilterCorrection
-- name    : QAlgorithms.Papers.Independent.Information100.P67.exponentialFilterCorrection
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:00:53.768673+00:00
-- url     : https://prove2.me/theorems/3fbe1ea7-555f-4944-bb86-7613111d4b4e
-- title:
--   Unnumbered quantitative consequence: exponentially small error correction (6.19)
-- statement:
--   Let $a_A,d_F\ge1$ be fixed integer dimensions and $c>0$. Define $b(n,\delta)$ by (6.11)–(6.12), using $g_n=(n+1)^{a_A^2}$ and $c_F=8\log_2(2d_F+1)$. Then
--
--   $$\limsup_{n\to\infty}\frac{b(n,2^{-cn})}{n}\le c_F\sqrt{8c}+8c.$$
--
--   The Lean statement uses the equivalent assertion that, for every $\eta>0$, this ratio is at most the displayed bound plus $\eta$ for all sufficiently large positive $n$. The explicit formula for $b$ is defined for every positive $\delta$, so the finitely many terms with $\delta\ge1/2$ cause no problem. The correction is not asserted to be $o(n)$ for fixed $c$.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 31, Unnumbered quantitative consequence: exponentially small error correction (6.19)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Exponentially small error correction (6.19), PDF p.31. The eventual
upper-bound formulation is equivalent to the displayed limsup inequality. -/
theorem exponentialFilterCorrection (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (c : ℝ) (hc : 0 < c) :
    ∀ eta : ℝ, 0 < eta → ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n ≥ n0,
      filterDimensionCorrection a d n (Real.rpow 2 (-c * n)) / (n : ℝ) ≤
        entropyDimensionConstant d * Real.sqrt (8 * c) + 8 * c + eta := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
