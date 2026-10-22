-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_remark_3
-- name    : QMCProduct.HalfApprox.remark_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:05.010887+00:00
-- url     : https://prove2.me/theorems/98152f48-372a-4be6-805f-75ef361cfebc
-- title:
--   Remark 3, p. 19 — at γ = 0.911 the large edges L of Algorithm 4 form a matching
-- statement:
--   Let $G$ be a graph on $n$ qubits, $\widetilde\rho$ a 2-positive pseudo-density with edge values $v_{ij}$, and $\gamma=0.911$. The set of large edges
--   $$L=\{ij\in E:\ v_{ij}>\gamma\}$$
--   is a matching: two distinct edges of $L$ share no endpoint.
--
--   This is what makes the output (5) of Algorithm 4 a product of states on disjoint qubits, and it is used in the analysis of edges adjacent to $L$.
--
--   **Formalization Note** Each undirected edge of $L$ is represented once, as an ordered pair $(i,j)$ with $i<j$; the conclusion states that neither endpoint of one pair equals either endpoint of the other. Only 2-positivity of $\widetilde\rho$ is assumed, not optimality, since the remark follows from Fact 2.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 19, Remark 3

import Definitions.Def_QMCProduct_HalfApprox_Algorithm

set_option autoImplicit false

namespace QMCProduct.HalfApprox

/-- Remark 3, p. 19: at `γ = 0.911` the large edges of Algorithm 4 form a matching. -/
theorem remark_3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ρt : Op n) (hρ : IsPseudoDensity 2 ρt)
    (e f : Fin n × Fin n) (he : e ∈ large G ρt (911 / 1000 : ℝ))
    (hf : f ∈ large G ρt (911 / 1000 : ℝ)) (hef : e ≠ f) :
    e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by sorry

end QMCProduct.HalfApprox
