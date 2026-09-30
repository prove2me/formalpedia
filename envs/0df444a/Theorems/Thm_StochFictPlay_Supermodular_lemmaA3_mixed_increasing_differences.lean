-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_lemmaA3_mixed_increasing_differences
-- name    : StochFictPlay.Supermodular.lemmaA3_mixed_increasing_differences
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:19:08.60348+00:00
-- url     : https://prove2.me/theorems/ead728a2-da6b-4df5-9e77-63c9351696a7
-- title:
--   Lemma A.3 — increasing differences against ordered mixed strategies
-- statement:
--   Consider a two player game in which player 1 has $n_1$ and player 2 has $n_2$ ordered strategies, and write player 1's payoffs as the matrix $A \in \mathbb R^{n_1 \times n_2}$, $A_{ik} = u^1(i,k)$. Suppose the game is strictly supermodular for player 1: for $i < j$, the map $k \mapsto A_{jk} - A_{ik}$ is strictly increasing. Let $x^2, y^2$ be mixed strategies of player 2 with
--   $$T^2 y^2 \ge T^2 x^2 \quad\text{and}\quad y^2 \ne x^2.$$
--   Then $(A y^2)_i - (A x^2)_i$ is strictly increasing in $i$.
--
--   So the increasing differences property of a supermodular game persists when the opponent's pure strategies are replaced by stochastically ordered mixed strategies. It is the key step in the proofs of Theorems 5.1 and 5.4.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 28, Lemma A.3 (setting of the proof of Theorem 5.1)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_StochOrder

namespace StochFictPlay.Supermodular

/-- Lemma A.3 (Hofbauer–Sandholm 2002, manuscript p. 28), for the two player reduction used in
the proof of Theorem 5.1: player 1's payoffs form the matrix `A` with `A i k = u¹(i, k)`, and
strict supermodularity says that `k ↦ A j k − A i k` is strictly increasing whenever `i < j`.
If player 2's mixed strategies satisfy `T² y² ≥ T² x²` and `y² ≠ x²`, then
`(A y²)_i − (A x²)_i` is strictly increasing in `i`. -/
theorem lemmaA3_mixed_increasing_differences {n₁ n₂ : ℕ} (A : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hA : ∀ i j : Fin n₁, i < j → StrictMono (fun k : Fin n₂ => A j k - A i k))
    (x y : Fin n₂ → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n₂)) (hy : y ∈ stdSimplex ℝ (Fin n₂))
    (hT : Tco x ≤ Tco y) (hne : y ≠ x) :
    StrictMono (fun i : Fin n₁ => Matrix.mulVec A y i - Matrix.mulVec A x i) := by sorry

end StochFictPlay.Supermodular
