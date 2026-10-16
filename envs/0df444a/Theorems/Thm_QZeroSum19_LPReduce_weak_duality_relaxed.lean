-- Prove2me | Theorems.Thm_QZeroSum19_LPReduce_weak_duality_relaxed
-- name    : QZeroSum19.LPReduce.weak_duality_relaxed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:02.424657+00:00
-- url     : https://prove2.me/theorems/2a5fff7b-5199-46ab-b814-50e57b7103fc
-- title:
--   Proof of Lemma 12, p. 14 — weak duality on the relaxed constraints: bᵀŷ ≤ (c + κe)ᵀx* ≤ cᵀx* + rκ
-- statement:
--   Let $A \in \mathbb R^{n\times m}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, $r \in \mathbb R$ and $\kappa \ge 0$. Let $\hat y \in \mathbb R^m$ satisfy $\hat y \ge 0$ and the relaxed constraints $A\hat y \le c + \kappa e$, and let $x^*$ be feasible for the dual (5), $A^{\mathsf T}x^* \ge b$, $x^* \ge 0$, with $\sum_i x^*_i \le r$. Then
--   $$b^{\mathsf T}\hat y \le (c + \kappa e)^{\mathsf T}x^* \le c^{\mathsf T}x^* + r\kappa .$$
--
--   In the proof of Lemma 12 this is applied with $\kappa = 6R\varepsilon'''$ and an optimal dual solution $x^*$ with $c^{\mathsf T}x^* = \mathrm{OPT}$, giving $b^{\mathsf T}\hat y \le \mathrm{OPT} + 6Rr\varepsilon'''$.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 14, proof of Lemma 12, display bᵀŷ ≤ (c + e6Rε‴)ᵀx* ≤ OPT + 6Rrε‴

import Mathlib
import Definitions.Def_QZeroSum19_LPReduce_Setting

open Matrix

namespace QZeroSum19.LPReduce
theorem weak_duality_relaxed {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (r κ : ℝ) (yhat : Fin m → ℝ) (x : Fin n → ℝ) (hyhat : ∀ j, 0 ≤ yhat j)
    (hκ : 0 ≤ κ) (hAy : ∀ i, (A *ᵥ yhat) i ≤ c i + κ) (hx : IsDualFeasible A b x)
    (hxr : ∑ i, x i ≤ r) :
    b ⬝ᵥ yhat ≤ (fun i => c i + κ) ⬝ᵥ x ∧ (fun i => c i + κ) ⬝ᵥ x ≤ c ⬝ᵥ x + r * κ := by sorry
end QZeroSum19.LPReduce
