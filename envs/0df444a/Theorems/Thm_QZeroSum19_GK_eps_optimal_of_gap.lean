-- Prove2me | Theorems.Thm_QZeroSum19_GK_eps_optimal_of_gap
-- name    : QZeroSum19.GK.eps_optimal_of_gap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:13.673372+00:00
-- url     : https://prove2.me/theorems/ee1dc6b9-0158-45f2-8067-7131cdc089c5
-- title:
--   Proof of Lemma 1, p. 4 — if every gap (Ay)_i − (Aᵀx)_j ≤ ε for x ∈ Δn, y ∈ Δm, both strategies are ε-optimal
-- statement:
--   Let $A\in\mathbb R^{n\times m}$ be a matrix game with value $v^*=\min_{y\in\Delta^m}\max_i (Ay)_i$, and let $x\in\Delta^n$, $y\in\Delta^m$ be mixed strategies of Alice and Bob. If
--   $$(Ay)_i-(A^{\mathsf T}x)_j\le\varepsilon\qquad\text{for all } i\in[n],\ j\in[m],$$
--   then $x$ is $\varepsilon$-optimal for Alice ($A^{\mathsf T}x\ge(v^*-\varepsilon)e$) and $y$ is $\varepsilon$-optimal for Bob ($Ay\le(v^*+\varepsilon)e$).
--
--   This is the reduction with which the proof of Lemma 1 begins: it turns the convergence question into a bound on the gaps between the two players' payoff vectors at the normalized iterates.
--
--   **Formalization Note** The paper invokes strong duality; the implication itself requires only the inequalities $\min_j(A^{\mathsf T}x)_j\le v^*\le\max_i(Ay)_i$, so no duality hypothesis is added.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 4, proof of Lemma 1, first display

import Mathlib
import Definitions.Def_QZeroSum19_GK_Setting

open Matrix

namespace QZeroSum19.GK

/-- Proof of Lemma 1, p. 4, first display: for mixed strategies `x ∈ Δn`, `y ∈ Δm`, if every
gap `(Ay)_i − (Aᵀx)_j` is at most `ε`, then `x` and `y` are `ε`-optimal. -/
theorem eps_optimal_of_gap {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n))
    (hy : y ∈ stdSimplex ℝ (Fin m)) (h : ∀ i j, (A *ᵥ y) i - (Aᵀ *ᵥ x) j ≤ ε) :
    IsEpsOptimalAlice A ε x ∧ IsEpsOptimalBob A ε y := by sorry

end QZeroSum19.GK
