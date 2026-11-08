-- Prove2me | Theorems.Thm_SpencerEight_theorem_8_1
-- name    : SpencerEight.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:47.414574+00:00
-- url     : https://prove2.me/theorems/49e00c90-48b2-4d76-9edb-65c9e0b0c928
-- title:
--   Theorem 8.1 — signs of norm at most $7.879493715947\sqrt n$
-- statement:
--   Let $1\le N\le n$, and let $A_1,\dots,A_n\in\mathbb R^{N\times N}$ be symmetric matrices with $\|A_i\|\le1$. There are signs $\varepsilon_1,\dots,\varepsilon_n\in\{-1,1\}$ such that
--   $$\Bigl\|\sum_{i=1}^n\varepsilon_iA_i\Bigr\|\le7.879493715947\sqrt n<7.8795\sqrt n.$$
--
--   This is the existence bound of the source: the Matrix Spencer conjecture with an explicit constant below $8$, for every $n$.
--
--   Differences from the source:
--   - encoding: indices 1, …, n; ε_i ∈ {−1, 1} → Fin n; real ε i with ε i = 1 ∨ ε i = −1; reason: indexing and the embedding of the signs in ℝ; same instances
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Theorem 8.1, p.68 (PDF p.68)

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction
import Definitions.Def_SpencerEight_signedSum
open scoped Matrix.Norms.L2Operator

namespace SpencerEight

/-- Theorem 8.1 (Existence constant below 7.8795), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.68 (PDF p.68): for `1 ≤ N ≤ n` and symmetric contractions `A₁, …, A_n ∈ ℝ^{N×N}` there are signs with `‖∑ εᵢAᵢ‖ ≤ 7.879493715947 √n < 7.8795 √n`.

**Formalization Note** The norm is the L2 operator norm; the signs are the reals `1` and `-1`. The second inequality is kept as printed. -/
theorem theorem_8_1 {N n : ℕ} (hN : 1 ≤ N) (hNn : N ≤ n) (A : Fin n → Matrix (Fin N) (Fin N) ℝ)
    (hA : ∀ i, IsSymmContraction (A i)) :
    ∃ ε : Fin n → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ‖signedSum A ε‖ ≤ 7.879493715947 * Real.sqrt n ∧
      7.879493715947 * Real.sqrt n < 7.8795 * Real.sqrt n := by sorry

end SpencerEight
