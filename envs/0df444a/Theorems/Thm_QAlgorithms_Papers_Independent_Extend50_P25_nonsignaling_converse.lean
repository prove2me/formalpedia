-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_nonsignaling_converse
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.nonsignaling_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:31:12.904701+00:00
-- url     : https://prove2.me/theorems/d07fc9fc-0921-453a-9851-f10a17494951
-- title:
--   Theorem 7.5: finite-port nonsignaling converse
-- statement:
--   Fix $d\ge1$. For every integer $N\ge1$, the optimal deterministic PBT squared entanglement fidelity satisfies
--   $$F_d^*(N)\le1-\frac{d^2-1}{8N^2}\frac1{1+(d^2-2)/(2N)}.$$
--   Moreover, for this fixed $d$ there are $C_d>0$ and $N_0\ge1$ such that
--   $$F_d^*(N)\le1-\frac{d^2-1}{8N^2}+\frac{C_d}{N^3}\qquad(N\ge N_0).$$
--   This retains both the finite nonsignaling converse and its quantitative asymptotic consequence.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 51, Theorem 7.5: finite-port nonsignaling converse

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Theorem 7.5, PDF p.51, finite bound AND its fixed-d asymptotic consequence.
The finite denominator contains d^2-2, and stays positive at d=N=1. -/
theorem nonsignaling_converse (d : ℕ) (hd : 1 ≤ d) :
    (∀ N : ℕ, 1 ≤ N → pbtOptimalFidelity d N ≤
      1 - ((d : ℝ)^2-1)/(8*(N : ℝ)^2)/(1+((d : ℝ)^2-2)/(2*(N : ℝ)))) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0,
      pbtOptimalFidelity d N ≤ 1 - ((d : ℝ)^2-1)/(8*(N : ℝ)^2) + C/(N : ℝ)^3) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
