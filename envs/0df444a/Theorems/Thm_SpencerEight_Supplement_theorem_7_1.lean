-- Prove2me | Theorems.Thm_SpencerEight_Supplement_theorem_7_1
-- name    : SpencerEight.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:52:12.29291+00:00
-- url     : https://prove2.me/theorems/645ab751-68aa-47f4-af73-983c4316f2c7
-- title:
--   Theorem 7.1 — signs of norm at most $156000\sqrt n$ for $n$ symmetric contractions in $\mathbb R^{n\times n}$
-- statement:
--   For all symmetric matrices $A_1,\dots,A_n\in\mathbb R^{n\times n}$ with $\|A_i\|\le1$ (operator norm) there is a vector $\varepsilon\in\{-1,1\}^n$ satisfying
--   $$
--   \Bigl\|\sum_{i=1}^n\varepsilon_iA_i\Bigr\|\le156000\sqrt n.
--   $$
--
--   This is the paper's second proof (Section 7), the formal version of its Theorem 1.1: the same partial-coloring structure with every constant tracked, which the algorithms of Sections 9–12 implement. The mission's goal, Theorem 8.1, gives the constant $7.879493715947$.
--
--   **Formalization Note** "Symmetric with $\|A_i\|\le1$" is the base mission's `IsSymmContraction`. No lower bound on $n$ is assumed, as printed (for $n=0$ the claim is trivial).
--
--   Differences from the source:
--   - encoding: indices 1, …, n; ε ∈ {−1, 1}ⁿ → Fin n; real ε i with ε i = 1 ∨ ε i = −1; reason: indexing and the embedding of the signs in ℝ; same instances
--   - generalization: matrix dimensions are positive integers under the paper's Section 4.1 convention → n ranges over all natural numbers, including 0; reason: the added n = 0 instance has the unique empty signing and zero signed sum, and the statement specializes unchanged to every positive n allowed by the source
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Theorem 7.1, p.63 (PDF p.63)

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction
import Definitions.Def_SpencerEight_signedSum
open scoped Matrix.Norms.L2Operator

namespace SpencerEight.Supplement

/-- Theorem 7.1 (Matrix Spencer discrepancy bound, formal version of Theorem 1.1), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…),
p.63 (PDF p.63): for all symmetric matrices `A₁, …, A_n ∈ ℝ^{n×n}` with `‖Aᵢ‖ ≤ 1` there is
`ε ∈ {−1,1}ⁿ` with `‖∑ᵢ εᵢ Aᵢ‖ ≤ 156000 √n`.

**Formalization Note** The norm is the L2 operator norm; "symmetric with `‖Aᵢ‖ ≤ 1`" is the base mission's
`IsSymmContraction`; the signs are the reals `1` and `-1`. No lower bound on `n` is assumed, as printed. -/
theorem theorem_7_1 (n : ℕ) (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, IsSymmContraction (A i)) :
    ∃ ε : Fin n → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ‖signedSum A ε‖ ≤ 156000 * Real.sqrt n := by sorry

end SpencerEight.Supplement
