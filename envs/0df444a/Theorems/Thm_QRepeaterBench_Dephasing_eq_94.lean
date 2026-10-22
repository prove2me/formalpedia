-- Prove2me | Theorems.Thm_QRepeaterBench_Dephasing_eq_94
-- name    : QRepeaterBench.Dephasing.eq_94
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:35.898087+00:00
-- url     : https://prove2.me/theorems/dc235c3d-2275-4d9b-8999-4ed304fe6806
-- title:
--   Eq. (94) — Φ(P_d) ≤ S(ρ_{P_d}‖σ̃) = log₂ d − H(P)
-- statement:
--   Let $d\ge2$ and $p\in[0,1]$. The entanglement flux of the qudit dephasing channel is bounded by the relative entropy of its Choi matrix with respect to $\tilde\sigma$, which equals $\log_2 d-H(\mathbf P)$:
--
--   $$\Phi(\mathcal P_d)\le S(\rho_{\mathcal P_d}\|\tilde\sigma)=\log_2 d-H(\mathbf P).$$
--
--   This is the upper bound on the two-way assisted capacities of the channel; it combines Eqs. (91) and (93).
--
--   **Formalization Note** $\Phi$ and the relative entropy take values in $[0,\infty]$; the right side is embedded with `ENNReal.ofReal`, which loses nothing since $H(\mathbf P)\le\log_2 d$.
-- source:
--   Pirandola & Laurenza, General Benchmarks for Quantum Repeaters, arXiv:1512.04945v2, p. 11, Eq. (94)

import Mathlib
import Definitions.Def_QRepeaterBench_Dephasing_Model

open scoped Matrix ENNReal

namespace QRepeaterBench.Dephasing
theorem eq_94 (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : flux d (dephasing d p) ≤ QAlgorithms.Papers.Independent.Information100.P54.relativeEntropyBits (choi d (dephasing d p)) (sigmaTilde d p) ∧ QAlgorithms.Papers.Independent.Information100.P54.relativeEntropyBits (choi d (dephasing d p)) (sigmaTilde d p) = ENNReal.ofReal (Real.logb 2 (d : ℝ) - shannonEntropy (weight d p)) := by sorry
end QRepeaterBench.Dephasing
