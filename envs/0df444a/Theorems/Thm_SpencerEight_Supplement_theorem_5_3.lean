-- Prove2me | Theorems.Thm_SpencerEight_Supplement_theorem_5_3
-- name    : SpencerEight.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:51:41.267792+00:00
-- url     : https://prove2.me/theorems/9ebfd214-3486-4cb4-ad70-5f1fed9a46a6
-- title:
--   Theorem 5.3 — signs of norm at most $7\cdot10^9\sqrt n$ for $n$ symmetric contractions in $\mathbb R^{n\times n}$
-- statement:
--   For every integer $n\ge1$ and symmetric contractions $A_1,\dots,A_n\in\mathbb R^{n\times n}$ (symmetric with $\|A_i\|\le1$ in the operator norm) there exist signs $\varepsilon\in\{-1,1\}^n$ such that
--   $$
--   \Bigl\|\sum_{i=1}^n\varepsilon_iA_i\Bigr\|\le7\cdot10^9\sqrt n.
--   $$
--
--   This is the paper's first proof of the Matrix Spencer conjecture (Section 5), by repeated partial coloring with an untracked constant. The mission's goal, Theorem 8.1, improves the constant to $7.879493715947$.
--
--   **Formalization Note** Symmetric contractions are the base mission's `IsSymmContraction`; the signed sum is its `signedSum`.
--
--   Differences from the source:
--   - encoding: indices 1, …, n; ε ∈ {−1, 1}ⁿ → Fin n; real ε i with ε i = 1 ∨ ε i = −1; reason: indexing and the embedding of the signs in ℝ; same instances
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Theorem 5.3, p.41 (PDF p.41)

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction
import Definitions.Def_SpencerEight_signedSum
open scoped Matrix.Norms.L2Operator

namespace SpencerEight.Supplement

/-- Theorem 5.3 (Matrix Spencer discrepancy), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.41 (PDF p.41): for every integer
`n ≥ 1` and symmetric contractions `A₁, …, A_n ∈ ℝ^{n×n}` there is `ε ∈ {−1,1}ⁿ` with
`‖∑ᵢ εᵢ Aᵢ‖ ≤ 7·10⁹ √n`.

**Formalization Note** The norm is the L2 operator norm; a symmetric contraction is the base mission's
`IsSymmContraction` (symmetric, `‖A‖ ≤ 1`); the signs are the reals `1` and `-1`; `7·10⁹ = 7000000000`. -/
theorem theorem_5_3 (n : ℕ) (hn : 1 ≤ n) (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, IsSymmContraction (A i)) :
    ∃ ε : Fin n → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ‖signedSum A ε‖ ≤ 7000000000 * Real.sqrt n := by sorry

end SpencerEight.Supplement
