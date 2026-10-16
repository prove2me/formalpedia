-- Prove2me | Theorems.Thm_QZeroSum19_LPReduce_h_near_half
-- name    : QZeroSum19.LPReduce.h_near_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:41.763862+00:00
-- url     : https://prove2.me/theorems/7d142611-6957-45d4-b981-60ab5b9d47cc
-- title:
--   Proof of Lemma 12, p. 14 — if y* = (y, z, h) ∈ Δ^{m+2} has A‴y* ≤ 2ε‴, then |h − 1/2| ≤ ε‴
-- statement:
--   Let $A'''$ be the game matrix (6) (second row $(-e^{\mathsf T}, -1, 1)$) for arbitrary data $A, b, c, \alpha, R$, and let $\kappa \in \mathbb R$. If $y^* = (y, z, h) \in \Delta^{m+2}$ satisfies $A'''y^* \le 2\kappa$ entrywise, then
--   $$\Bigl|h - \frac12\Bigr| \le \kappa .$$
--
--   In the proof of Lemma 12 this is applied with $\kappa = \varepsilon'''$: an approximately optimal strategy of the game (6) puts weight close to $1/2$ on the homogenizing variable $h$.
--
--   **Formalization Note** $h$ is the column `inr 1` of `Fin m ⊕ Fin 2`. Only the first two rows of (6) enter.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 14, proof of Lemma 12, second case ("This implies that |h − 1/2| ≤ ε‴")

import Mathlib
import Definitions.Def_QZeroSum19_LPReduce_Setting

open Matrix

namespace QZeroSum19.LPReduce
theorem h_near_half {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R κ : ℝ) (y' : Fin m ⊕ Fin 2 → ℝ) (hy' : y' ∈ stdSimplex ℝ (Fin m ⊕ Fin 2))
    (hle : ∀ k, (gameMatrix A b c α R *ᵥ y') k ≤ 2 * κ) :
    |y' (Sum.inr 1) - 1 / 2| ≤ κ := by sorry
end QZeroSum19.LPReduce
