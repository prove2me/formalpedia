-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_optimized_success_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.optimized_success_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:27:04.165866+00:00
-- url     : https://prove2.me/theorems/da4d0ee2-1930-4190-b6a0-462c2f468529
-- title:
--   Remark 5.1: optimized probabilistic PBT expansion
-- statement:
--   Fix $d\ge1$. For the heralded PBT success probability optimized over both resource and measurement,
--   $$p_d^*(N)=1-\frac{d^2-1}{d^2-1+N}\quad(N\ge1),\qquad p_d^*(N)=1-\frac{d^2-1}N+o(N^{-1}).$$
--   For every positive remainder tolerance, the second formula holds for all sufficiently large $N$ at that fixed $d$. It describes the improved optimized-resource convergence without asserting a strict advantage at $d=1$.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 28, Remark 5.1: optimized probabilistic PBT expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Remark 5.1, PDF p.28: the fully optimized physical success probability, its
exact expression and fixed-d o(1/N) expansion, including the zero-coefficient d=1 case. -/
theorem optimized_success_expansion (d : ℕ) (hd : 1 ≤ d) :
    (∀ N : ℕ, 1 ≤ N → pbtOptimalSuccess d N = 1 - ((d : ℝ)^2-1)/((d : ℝ)^2-1+N)) ∧
    (∀ eta : ℝ, 0 < eta → ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0,
      |pbtOptimalSuccess d N - (1-((d : ℝ)^2-1)/(N : ℝ))| ≤ eta/(N : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
