-- Prove2me | Theorems.Thm_QZeroSum19_LPReduce_certificate
-- name    : QZeroSum19.LPReduce.certificate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:44.093277+00:00
-- url     : https://prove2.me/theorems/08206bf6-470c-4229-a12e-b9b5dd323ccb
-- title:
--   Proof of Lemma 12, p. 14 — a primal point with Σy ≤ R and bᵀy ≥ α gives ŷ = (y/(2R), 1/2 − Σy/(2R), 1/2) ∈ Δ^{m+2} with A‴ŷ ≤ 0
-- statement:
--   Let $A \in \mathbb R^{n\times m}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, $\alpha \in \mathbb R$ and $R > 0$, and let $A'''$ be the game matrix (6) (with second row $(-e^{\mathsf T}, -1, 1)$). Suppose $y \in \mathbb R^m$ satisfies $Ay \le c$, $y \ge 0$, $\sum_j y_j \le R$ and $b^{\mathsf T}y \ge \alpha$. Put
--   $$\hat y = \Bigl(\frac{y}{2R},\ \frac12 - \frac{\sum_j y_j}{2R},\ \frac12\Bigr) \in \mathbb R^{m+2}.$$
--   Then $\hat y$ lies in the simplex $\Delta^{m+2}$ and
--   $$A'''\hat y = \begin{pmatrix} 0 \\ 0 \\ (-b^{\mathsf T}y + \alpha)/(2R) \\ (Ay - c)/(2R)\end{pmatrix} \le 0 .$$
--
--   This is the certificate of the first case of the proof of Lemma 12: if $\mathrm{OPT} \ge \alpha$, the game (6) has a strategy for the column player that keeps every row payoff nonpositive.
--
--   **Formalization Note** The conclusion states $\hat y \in \Delta^{m+2}$ and that every entry of $A'''\hat y$ is at most $0$; the explicit values of the entries are not part of the statement. The columns are indexed by `Fin m ⊕ Fin 2`, with $z$ at `inr 0` and $h$ at `inr 1`.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 14, proof of Lemma 12, first case (definition of ŷ and the display A‴ŷ ≤ 0)

import Mathlib
import Definitions.Def_QZeroSum19_LPReduce_Setting

open Matrix

namespace QZeroSum19.LPReduce
theorem certificate {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (hR : 0 < R) (y : Fin m → ℝ) (hy : IsPrimalFeasible A c y)
    (hsum : ∑ j, y j ≤ R) (hby : α ≤ b ⬝ᵥ y) :
    let yhat : Fin m ⊕ Fin 2 → ℝ :=
      Sum.elim (fun j => y j / (2 * R)) ![1 / 2 - (∑ j, y j) / (2 * R), 1 / 2]
    yhat ∈ stdSimplex ℝ (Fin m ⊕ Fin 2) ∧ ∀ k, (gameMatrix A b c α R *ᵥ yhat) k ≤ 0 := by sorry
end QZeroSum19.LPReduce
