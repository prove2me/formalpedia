-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_optimal_infidelity_theta
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.optimal_infidelity_theta
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:14:58.28809+00:00
-- url     : https://prove2.me/theorems/834babdb-e165-4f89-b8af-e688be03c83e
-- title:
--   Theorem 1.1 / original paper-result seed: optimal deterministic PBT infidelity
-- statement:
--   Fix an integer local dimension $d\ge2$. Let $F_d^*(N)$ be the supremum of squared entanglement fidelity over all deterministic port-based teleportation protocols with $N$ ports, arbitrary shared resource states and Alice's finite ancillas. There are constants $c_d,C_d>0$ and $N_0\ge1$ such that for every $N\ge N_0$,
--   $$\frac{c_d}{N^2}\le1-F_d^*(N)\le\frac{C_d}{N^2}.$$
--   This identifies the optimal fixed-dimension order of infidelity.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 4, Theorem 1.1 / original paper-result seed: optimal deterministic PBT infidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Theorem 1.1, PDF p.4: fixed nontrivial dimension, optimal infidelity Theta(N^-2).
Printed: arbitrary fixed local dimension. Changed: d>=2. The d=1 identity system
has zero infidelity, so a positive Theta lower bound needs this minimal correction. -/
theorem optimal_infidelity_theta (d : ℕ) (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0,
      c / (N : ℝ)^2 ≤ 1 - pbtOptimalFidelity d N ∧
      1 - pbtOptimalFidelity d N ≤ C / (N : ℝ)^2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
