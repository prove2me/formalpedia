-- Prove2me | Theorems.Thm_QZeroSum19_LPReduce_exists_strategy_le
-- name    : QZeroSum19.LPReduce.exists_strategy_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:50.626029+00:00
-- url     : https://prove2.me/theorems/05866216-841f-4fbc-a2f3-ee9d88594505
-- title:
--   Proof of Lemma 12, p. 14 — if λ* ≤ t, some strategy y* ∈ Δ has every row payoff (My*)ₖ ≤ t
-- statement:
--   Let $M$ be a real matrix with finite row set $I$ and finite nonempty column set $K$, let $\lambda^*(M) = \inf_{y \in \Delta^K} \max_{i} (My)_i$ be its game value, and let $t \in \mathbb R$. If $\lambda^*(M) \le t$, then there is a strategy $y^* \in \Delta^K$ with
--   $$(My^*)_k \le t \quad\text{for every row } k .$$
--
--   In the proof of Lemma 12 this is the step "if $\lambda^* \le 2\varepsilon'''$ and $y^* = (y, z, h)$ is a strategy with this value, then $A'''y^* \le 2\varepsilon'''$", applied to $M = A'''$ and $t = 2\varepsilon'''$: the value of the game is achieved by some strategy of the column player.
--
--   **Formalization Note** The statement is posed for any finite matrix, with the column type nonempty so that the simplex is nonempty; the game matrix (6) has $m + 2 \ge 2$ columns.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 14, proof of Lemma 12, second case ("y* = (y, z, h) is a strategy with this value, then … A‴y* ≤ 2ε‴")

import Mathlib
import Definitions.Def_QZeroSum19_LPReduce_Setting

open Matrix

namespace QZeroSum19.LPReduce
theorem exists_strategy_le {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (M : Matrix ι κ ℝ) (t : ℝ) (ht : QZeroSum19.GK.gameValue M ≤ t) :
    ∃ y ∈ stdSimplex ℝ κ, ∀ k, (M *ᵥ y) k ≤ t := by sorry
end QZeroSum19.LPReduce
