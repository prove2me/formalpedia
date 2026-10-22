-- Prove2me | Theorems.Thm_QZeroSum19_GK_potential_update
-- name    : QZeroSum19.GK.potential_update
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:08.778436+00:00
-- url     : https://prove2.me/theorems/374a4076-6fd8-4ee0-ab6d-394ffa36dd97
-- title:
--   Proof of Lemma 1, p. 4 — Φ(t+1) = Φ(t)(Σ_j p_j e^{−ηA_bj})(Σ_i q_i e^{ηA_ia})
-- statement:
--   For a matrix $A\in\mathbb R^{n\times m}$ and vectors $x\in\mathbb R^n$, $y\in\mathbb R^m$ write
--   $$\Phi(x,y)=\Big(\sum_{j\in[m]}e^{-(A^{\mathsf T}x)_j}\Big)\Big(\sum_{i\in[n]}e^{(Ay)_i}\Big),\qquad p=G(-A^{\mathsf T}x),\quad q=G(Ay),$$
--   with $G$ the Gibbs distribution. For every step $\eta\in\mathbb R$ and moves $a\in[m]$, $b\in[n]$, the potential after the update $x\mapsto x+\eta e_b$, $y\mapsto y+\eta e_a$ is
--   $$\Phi(x+\eta e_b,\ y+\eta e_a)=\Phi(x,y)\Big(\sum_{j\in[m]}p_j e^{-\eta A_{bj}}\Big)\Big(\sum_{i\in[n]}q_i e^{\eta A_{ia}}\Big).$$
--
--   This identity expresses one iteration of Algorithm 1 as a multiplicative change of the potential, which is what the expectation bound of the next step controls.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 4, proof of Lemma 1, the Φ(t + 1) display

import Mathlib
import Definitions.Def_QZeroSum19_GK_Setting

open Matrix

namespace QZeroSum19.GK

/-- Proof of Lemma 1, p. 4, the `Φ(t + 1)` display: after the update `x ↦ x + η e_b`,
`y ↦ y + η e_a`,
`Φ' = Φ · (Σ_j p_j e^{−η A_bj}) · (Σ_i q_i e^{η A_ia})` with `p = G(−Aᵀx)`, `q = G(Ay)`. -/
theorem potential_update {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ)
    (y : Fin m → ℝ) (η : ℝ) (a : Fin m) (b : Fin n) :
    potential A (x + η • Pi.single b 1) (y + η • Pi.single a 1) =
      potential A x y * (∑ j, gibbs (-(Aᵀ *ᵥ x)) j * Real.exp (-η * A b j)) *
        (∑ i, gibbs (A *ᵥ y) i * Real.exp (η * A i a)) := by sorry

end QZeroSum19.GK
