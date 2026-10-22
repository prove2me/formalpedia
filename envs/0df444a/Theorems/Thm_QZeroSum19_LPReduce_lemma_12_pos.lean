-- Prove2me | Theorems.Thm_QZeroSum19_LPReduce_lemma_12_pos
-- name    : QZeroSum19.LPReduce.lemma_12_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:34.643048+00:00
-- url     : https://prove2.me/theorems/66d95268-fa3d-4310-916b-2a3c3c54a1e4
-- title:
--   Proof of Lemma 12, p. 14 — case λ* > 0: OPT < α
-- statement:
--   Let the LP pair (4)/(5) with data $A \in \mathbb R^{n\times m}$, $b$, $c$ satisfy the standing assumptions of §4 with constants $R$, $r$ and optimal value $\mathrm{OPT}$, let $\alpha \in \mathbb R$, and let $\lambda^*$ be the value of the game (6) (second row $(-e^{\mathsf T}, -1, 1)$). Then
--   $$\lambda^* > 0 \implies \mathrm{OPT} < \alpha .$$
--
--   This is the first case of the proof of Lemma 12: a positive game value certifies that the LP cannot reach the objective level $\alpha$.
--
--   **Formalization Note** $\lambda^*$ is the infimum over the column player's simplex $\Delta^{m+2}$ of the largest entry of $A'''y'''$. No bound on $\alpha$ is needed in this case.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 14, proof of Lemma 12, first case ("which is a contradiction, hence OPT < α")

import Mathlib
import Definitions.Def_QZeroSum19_LPReduce_Setting

open Matrix

namespace QZeroSum19.LPReduce
theorem lemma_12_pos {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (R r OPT α : ℝ) (hLP : LPStanding A b c R r OPT) :
    0 < QZeroSum19.GK.gameValue (gameMatrix A b c α R) → OPT < α := by sorry
end QZeroSum19.LPReduce
