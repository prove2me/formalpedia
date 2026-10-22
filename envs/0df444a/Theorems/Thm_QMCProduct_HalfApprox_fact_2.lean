-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_fact_2
-- name    : QMCProduct.HalfApprox.fact_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:28.840163+00:00
-- url     : https://prove2.me/theorems/dc8bcd86-784c-477e-b848-a19cb13f550a
-- title:
--   Fact 2, p. 16 — if vij > γ = 0.911, then every adjacent pair ik has vik < 1/3
-- statement:
--   Let $\widetilde\rho$ be a level-2 pseudo-density and let $i,j,k$ be three distinct qubits. At the paper's threshold $\gamma=0.911$,
--   $$v_{ij}>0.911\quad\Longrightarrow\quad v_{ik}<\frac13.$$
--   Thus an edge adjacent to a large edge has a small relaxed value. This is the monogamy fact used to show that large edges form a matching and to bound the remaining edge class.
--
--   **Formalization Note** The proof on p. 22 uses no graph property, so the statement quantifies over any distinct three qubits. The threshold is the paper's decimal $911/1000$.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, pp. 16, 22, Fact 2 and its proof

import Definitions.Def_QMCProduct_HalfApprox_Basic

set_option autoImplicit false

namespace QMCProduct.HalfApprox

/-- Fact 2, pp. 16, 22, at the paper's chosen threshold. -/
theorem fact_2 {n : ℕ} (ρt : Op n) (hρ : IsPseudoDensity 2 ρt)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlarge : (911 / 1000 : ℝ) < v ρt i j) :
    v ρt i k < 1 / 3 := by sorry

end QMCProduct.HalfApprox
