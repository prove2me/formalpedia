-- Prove2me | Theorems.Thm_QMaxCutBeyond_TwoQubit_eq_25
-- name    : QMaxCutBeyond.TwoQubit.eq_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:29.798161+00:00
-- url     : https://prove2.me/theorems/d4ac3aa7-4b7f-4cf2-9e6f-c0d47297a94f
-- title:
--   Eq. (25) — singlets on a matching, random bits elsewhere: average energy 3/2·m + 1/2·W
-- statement:
--   Let $G=(V,E,w)$ have nonnegative weights, $W=\sum_{e\in E}w_e$, let $M\subseteq E$ be a matching with $m=\sum_{e\in M}w_e$, and let $U\subseteq V$ be the vertices not incident to an edge of $M$. For $z\in\{0,1\}^U$ put
--   $$|\varphi_z\rangle=\Bigl(\bigotimes_{e=\{i,j\}\in M}\tfrac1{\sqrt2}(|01\rangle-|10\rangle)_{ij}\Bigr)\otimes|z\rangle_U .$$
--   Then, for $z$ uniformly random,
--   $$\mathbb E_z\bigl[\langle\varphi_z|H_G|\varphi_z\rangle\bigr]=2\sum_{e\in M}w_e+\frac12\Bigl(W-\sum_{e\in M}w_e\Bigr)=\frac32m+\frac12W .$$
--
--   Hence some $\varphi_z$, a tensor product of 1- and 2-qubit states, has energy at least $\frac32m+\frac12W$: the second candidate state of eq. (27).
--
--   **Formalization Note** The expectation is the average over all $2^{|U|}$ functions $z:U\to\{0,1\}$. The singlet on $\{i,j\}$, $i<j$, has qubit $i$ first; the opposite order only flips the sign of $\varphi_z$.
-- source:
--   Anshu, Gosset & Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394v1, p. 10, eq. (25), proof of Theorem 3

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

/-- Eq. (25), p. 10: for a matching `M ⊆ E` with uncovered vertex set `U`, the average of
`⟨φ_z|H_G|φ_z⟩` over the `2^{|U|}` strings `z ∈ {0,1}^U` equals `3/2 m + 1/2 W`,
`m = Σ_{e∈M} w_e`. -/
theorem eq_25 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e)
    (M : Finset (Sym2 (Fin n))) (hMG : M ⊆ G.edgeFinset) (hM : IsEdgeMatching M) :
    (∑ z : ↥(uncovered M) → Fin 2, energy (hamiltonian G w) (matchingState M z)) /
        (2 : ℝ) ^ (uncovered M).card =
      3 / 2 * (∑ e ∈ M, w e) + 1 / 2 * totalWeight G w := by sorry

end QMaxCutBeyond.TwoQubit
