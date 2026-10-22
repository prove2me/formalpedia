-- Prove2me | Theorems.Thm_QMCTriFree_Circuit_lemma_10
-- name    : QMCTriFree.Circuit.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:53.046792+00:00
-- url     : https://prove2.me/theorems/fa653e57-f6dd-4251-9d09-328fd914c88a
-- title:
--   Lemma 10 — the energy of a product state on $h_{ij}$ is $\tfrac12(1-\vec v_i\cdot\vec v_j)$
-- statement:
--   Let $\vec v_k\in S^2\subset\mathbb R^3$ be the Bloch vector of the single-qubit state $|v_k\rangle$, $k\in V$, and let $\rho=\bigotimes_k\tfrac12(1+\vec v_k\cdot\vec\sigma)$ be the product state. For distinct vertices $i\ne j$,
--   $$\operatorname{Tr}(h_{ij}\rho)=\tfrac12\bigl(1-\vec v_i\cdot\vec v_j\bigr)=E_{ij}.$$
--
--   This identifies the energy of the unentangled starting state of the circuit on each edge, the quantity $E_{ij}$ that appears as a factor in Lemmas 12 and 18.
--
--   **Formalization Note** The pure product state $\bigotimes_k|v_k\rangle$ is represented by its density matrix, so no phase is chosen; the middle expression $2\langle v_iv_j|\psi^-_{ij}\rangle\langle\psi^-_{ij}|v_iv_j\rangle$ of the paper is the same number and is not restated.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, p. 10, Lemma 10

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Algorithm

set_option autoImplicit false

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory

namespace QMCTriFree.Circuit

/-- King, arXiv:2209.02589v3, p. 10, Lemma 10: the energy of the product state
`⊗_k |v_k⟩⟨v_k|` on the term `h_ij` is `½(1 − v⃗_i · v⃗_j)`. -/
theorem lemma_10 {n : ℕ} (v : Fin n → Fin 3 → ℝ) (hv : ∀ k, v k ⬝ᵥ v k = 1)
    (i j : Fin n) (hij : i ≠ j) :
    energy (hEdge i j) (rho0 v) = (1 / 2 : ℝ) * (1 - v i ⬝ᵥ v j) := by sorry

end QMCTriFree.Circuit
