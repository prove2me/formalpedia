-- Prove2me | Theorems.Thm_QMaxCutBeyond_TwoQubit_eq_10
-- name    : QMaxCutBeyond.TwoQubit.eq_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:04.984618+00:00
-- url     : https://prove2.me/theorems/6eaf37be-0981-4ba8-87bb-e5077ecc5080
-- title:
--   Eq. (10) — the Laplacian of a weighted star satisfies ‖L(G)‖ ≤ Σ_e w_e + max_e w_e
-- statement:
--   Let $G=(V,E,w)$ be a star graph (every edge contains a fixed centre $c$) with nonnegative weights, and let $L(G)$ be its weighted Laplacian. Then for every real vector $x\in\mathbb R^V$
--   $$x^{\mathsf T}L(G)\,x\;\le\;\Bigl(\sum_{e\in E}w_e+\max_{e\in E}w_e\Bigr)\,\|x\|^2 ,$$
--   that is, $\|L(G)\|\le\sum_{e\in E}w_e+\max_{e\in E}w_e$.
--
--   In the proof of Lemma 1 the star Hamiltonian restricted to the Hamming-weight-one subspace is the Laplacian, so this bound is the spectral input of Lemma 1.
--
--   **Formalization Note** $L(G)$ is real symmetric and positive semidefinite, so its norm is its largest eigenvalue, the maximum of the Rayleigh quotient; the statement is that quotient bound. The graph may have isolated vertices besides the star; $\max_{e\in E}w_e=0$ if $E=\emptyset$.
-- source:
--   Anshu, Gosset & Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394v1, p. 7, eq. (10), proof of Lemma 1

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

open Matrix

/-- Eq. (10), p. 7: for a star graph with nonnegative weights, the Laplacian satisfies
`‖L(G)‖ ≤ Σ_{e∈E} w_e + max_{e∈E} w_e`, stated as the Rayleigh-quotient bound for the
(positive semidefinite, real symmetric) Laplacian. -/
theorem eq_10 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e) (c : Fin n) (hstar : IsStar G c)
    (x : Fin n → ℝ) :
    x ⬝ᵥ (laplacian G w *ᵥ x) ≤ (totalWeight G w + maxEdgeWeight G w) * (x ⬝ᵥ x) := by sorry

end QMaxCutBeyond.TwoQubit
