-- Prove2me | Theorems.Thm_QMCTriFree_Circuit_lemma_18
-- name    : QMCTriFree.Circuit.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:46.627656+00:00
-- url     : https://prove2.me/theorems/e3572275-0d8e-46e4-bb36-d1bb4446defe
-- title:
--   Lemma 18 — with $\theta_{ij}=\tfrac12\arcsin\beta x_{ij}$ for $x_{ij}\ge0$, the expected edge energy obeys the lower bound (17)
-- statement:
--   Let $(V,\{w_{ij}\})$ be a triangle-free weighted graph, $M$ feasible for $\mathrm{Lasserre}_2(H)$ with edge values $x_{ij}$, $\beta\in[0,1]$, and define
--   $$\theta_{ij}=\begin{cases}\tfrac12\arcsin\beta x_{ij}&x_{ij}\ge0\\0&\text{otherwise.}\end{cases}$$
--   For any product state with Bloch vectors $\vec v_k\in S^2$, the random commuting circuit of Algorithm 17 with these angles gives, on every edge $(i,j)$ and averaged over the random $P_k$,
--   $$\langle h_{ij}\rangle\ \ge\ E_{ij}\Bigl(\tfrac12+\tfrac12\bigl(1-\beta^2(1-x_{ij})^2\bigr)+\tfrac2\pi\beta x_{ij}\Bigl(\sqrt{1-\beta^2}+\bigl(1-\sqrt{1-\beta^2}\bigr)x_{ij}\Bigr)\Bigr).$$
--
--   This is the per-edge guarantee of the entangling stage; multiplied by the rounding guarantee of Lemma 13 it yields the function $F(\beta;x)$.
--
--   **Formalization Note** Stated as eq. (17), with the factor $E_{ij}$; the subsequent bound $\langle h_{ij}\rangle\ge F(\beta;x_{ij})$ on the page is part of the goal's proof. The product state is fixed and arbitrary; the expectation is over the equator draws only.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, p. 17, Lemma 18, eqs. (16)–(17)

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Algorithm

set_option autoImplicit false

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory

namespace QMCTriFree.Circuit

/-- King, arXiv:2209.02589v3, p. 17, Lemma 18, eq. (17): on a triangle-free graph, with a
feasible `M`, any `β ∈ [0, 1]`, the angles (16) `θ_ij = ½ arcsin(β x_ij)` (`x_ij ≥ 0`), `0`
otherwise, and any product state of unit Bloch vectors, the expected energy on the edge term
`h_ij` (averaged over the equatorial `P_k`) is at least
`E_ij(½ + ½(1 − β²(1 − x_ij)²) + (2/π) β x_ij (√(1 − β²) + (1 − √(1 − β²)) x_ij))`. -/
theorem lemma_18 {n : ℕ} (w : Fin n → Fin n → ℝ) (hw : IsWeightedGraph w)
    (htf : IsTriangleFree w) (M : Matrix (P2 n) (P2 n) ℝ) (hM : IsFeasible M)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (v : Fin n → Fin 3 → ℝ) (hv : ∀ k, v k ⬝ᵥ v k = 1)
    (i j : Fin n) (hij : i ≠ j) (hwij : w i j ≠ 0) :
    Eij v i j * bracket β (xval M i j) ≤ avgEdgeEnergy w (thetaOf β M) v i j := by sorry

end QMCTriFree.Circuit
