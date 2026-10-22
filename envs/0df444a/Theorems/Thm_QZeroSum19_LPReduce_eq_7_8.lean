-- Prove2me | Theorems.Thm_QZeroSum19_LPReduce_eq_7_8
-- name    : QZeroSum19.LPReduce.eq_7_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:28.953001+00:00
-- url     : https://prove2.me/theorems/91b9bf46-53f2-4373-9698-954628d1a245
-- title:
--   Proof of Lemma 12, p. 14, (7)–(8) — for ŷ = 2Ry: bᵀŷ ≥ α − 6Rε‴ and Aŷ ≤ c + 6Rε‴ (under |α|, |cᵢ| ≤ R)
-- statement:
--   Let $A \in \mathbb R^{n\times m}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, $\alpha \in \mathbb R$, $R > 0$ with $|c_i| \le R$ for all $i$ and $|\alpha| \le R$, and let $\kappa \ge 0$. Let $A'''$ be the game matrix (6) (second row $(-e^{\mathsf T}, -1, 1)$), and let $y^* = (y, z, h) \in \Delta^{m+2}$ satisfy $A'''y^* \le 2\kappa$ entrywise. Put $\hat y = 2Ry \in \mathbb R^m$. Then
--   $$b^{\mathsf T}\hat y \ge \alpha - 6R\kappa, \qquad\qquad (7)$$
--   $$A\hat y \le c + 6R\kappa\, e. \qquad\qquad (8)$$
--
--   With $\kappa = \varepsilon'''$ these are the displays (7) and (8) of the proof of Lemma 12: the rescaled $y$-part of an approximately optimal strategy is an approximately feasible point of (4) whose objective is approximately at least $\alpha$.
--
--   **Formalization Note** The page's intermediate bounds $b^{\mathsf T}\hat y \ge \alpha - 2(\alpha + 2R)\varepsilon'''$ and $A\hat y \le c + 2(c + 2R)\varepsilon'''$ are valid as printed for $\alpha \ge 0$ and $c \ge 0$; for general signs they hold with $|\alpha|$ and $|c_i|$, and the final bounds $6R\varepsilon'''$ then need $|\alpha| \le R$ and $|c_i| \le R$. Only the final bounds (7) and (8) are stated. The hypothesis $|c_i| \le R$ is a standing assumption of §4 (p. 12); $|\alpha| \le R$ is added (the binary search of §4 runs over $-R \le \mathrm{OPT} \le R$, and (6) has entries in $[-1,1]$ only when $|\alpha| \le R$).
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 14, proof of Lemma 12, (7) and (8)

import Mathlib
import Definitions.Def_QZeroSum19_LPReduce_Setting

open Matrix

namespace QZeroSum19.LPReduce
theorem eq_7_8 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R κ : ℝ) (hR : 0 < R) (hc : ∀ i, |c i| ≤ R) (hα : |α| ≤ R) (hκ : 0 ≤ κ)
    (y' : Fin m ⊕ Fin 2 → ℝ) (hy' : y' ∈ stdSimplex ℝ (Fin m ⊕ Fin 2))
    (hle : ∀ k, (gameMatrix A b c α R *ᵥ y') k ≤ 2 * κ) :
    let yhat : Fin m → ℝ := fun j => 2 * R * y' (Sum.inl j)
    α - 6 * R * κ ≤ b ⬝ᵥ yhat ∧ ∀ i, (A *ᵥ yhat) i ≤ c i + 6 * R * κ := by sorry
end QZeroSum19.LPReduce
