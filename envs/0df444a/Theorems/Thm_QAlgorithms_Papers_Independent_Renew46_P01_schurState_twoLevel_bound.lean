-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P01_schurState_twoLevel_bound
-- name    : QAlgorithms.Papers.Independent.Renew46.P01.schurState_twoLevel_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:43:34.814692+00:00
-- url     : https://prove2.me/theorems/eb63e057-bc5f-47a5-92b0-305ec5487e32
-- title:
--   Individual Schur states require O(n²) active two-level rotations
-- statement:
--   There are positive absolute constants $C,L$ and an integer $n_0\ge2$ such that the following holds for every $n\ge n_0$ and every complete admissible Schur label $a$. The label specifies a sequential spin path and a root projection $M\in\{-J,-J+1,\ldots,J\}$. Let $\psi_a$ be its physical $n$-qubit Schur vector with the source real Condon–Shortley coefficients and the convention $|0\rangle=|-1/2\rangle$.
--
--   There exist a workspace size $w$ and a finite circuit $C_a$ of unitary two-level rotations, each embedded on named active wires, with
--
--   $$
--   |C_a|\le Cn^2,\qquad
--   \operatorname{arity}(G)\le L\lceil\log_2(n+1)\rceil\quad(G\in C_a),
--   \qquad
--   C_a|0^{n+w}\rangle=|\psi_a\rangle|0^w\rangle.
--   $$
--
--   All target labels are fixed before selecting the preparation circuit. Circuit length counts actual rotations on the active subregisters; spectator identities need not leave the full matrix globally two-level. This is the exact two-level preparation bound, with no Clifford+T approximation convention added.
-- source:
--   Generalised Coupling and An Elementary Algorithm for the Quantum Schur Transform, arXiv:2305.04069v3, PDF p. 26, Claim A.2: O(n^2) two-level rotations for individual Schur state

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P01

open scoped BigOperators ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF pp.26--27, Claim A.2: fixed-label Schur-state preparation has
O(n^2) active two-level rotations, each on O(log n) named wires. Constants
precede n and all complete target labels. The circuit starts from zero,
uses actual gate-list length, and leaves its workspace clean. There is
no arbitrary target-state gate and no assertion about Clifford+T error. -/
theorem schurState_twoLevel_bound :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∀ a : SchurLabel n,
        ∃ w : ℕ, ∃ c : Circuit twoLevelGates (n + w),
          (c.size : ℝ) ≤ C * (n : ℝ) ^ 2 ∧
          (∀ g ∈ c, (g.gate.arity : ℝ) ≤ L * (Nat.clog 2 (n + 1) : ℝ)) ∧
          act c.unitary (zeroKet (n + w)) = cleanVector w (schurState a) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P01

end
