-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_eq_12
-- name    : QMCProduct.HalfApprox.eq_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:17.638881+00:00
-- url     : https://prove2.me/theorems/99b73013-c56a-4c5d-b2dc-6332f7d8ddcd
-- title:
--   Equation (12), p. 19 — the state (I − Z⊗Z)/4 earns 1/2 ≥ µij/2 on a large edge
-- statement:
--   Let $\widetilde\rho$ be a level-2 pseudo-density on $n$ qubits and $i\ne j$ two qubits, with relaxed value $\mu_{ij}$ (Definition 12). For the large-edge output $\rho=(I-Z\otimes Z)/4$ on two qubits and the QMC term $(I-X\otimes X-Y\otimes Y-Z\otimes Z)/4$,
--   $$\operatorname{Tr}\Big[\frac{I-X\otimes X-Y\otimes Y-Z\otimes Z}{4}\,\rho\Big]=\frac12\ge\frac12\mu_{ij}.$$
--   This is the per-edge approximation for an edge selected into $L$.
--
--   **Formalization Note** The Lean item formalizes the printed two-qubit identity and the inequality $\frac12\ge\frac12\mu_{ij}$ for an arbitrary pair of distinct qubits of an $n$-qubit level-2 pseudo-density. Identifying $(I-Z\otimes Z)/4$ as the marginal of Algorithm 4's $n$-qubit output on a large edge belongs to the goal proof.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 19, equation (12)

import Definitions.Def_QMCProduct_HalfApprox_Algorithm

set_option autoImplicit false

namespace QMCProduct.HalfApprox

/-- Equation (12), p. 19: the printed two-qubit state `(I − Z⊗Z)/4` earns `1/2` on the QMC
term, and `1/2 ≥ µ_ij/2` for the edge values of a level-2 pseudo-density on `n` qubits. -/
theorem eq_12 {n : ℕ} (ρt : Op n) (hρ : IsPseudoDensity 2 ρt) (i j : Fin n) (hij : i ≠ j) :
    (hQMC (0 : Fin 2) (1 : Fin 2) *
      ((1 / 4 : ℂ) • (1 - Z (0 : Fin 2) * Z (1 : Fin 2)))).trace.re = 1 / 2 ∧
    (1 / 2 : ℝ) * mu ρt i j ≤ 1 / 2 := by sorry

end QMCProduct.HalfApprox
