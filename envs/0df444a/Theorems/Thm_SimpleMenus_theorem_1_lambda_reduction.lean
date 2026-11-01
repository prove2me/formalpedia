-- Prove2me | Theorems.Thm_SimpleMenus_theorem_1_lambda_reduction
-- name    : SimpleMenus.theorem_1_lambda_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:37:46.286275+00:00
-- url     : https://prove2.me/theorems/6ea35963-f6cd-4eae-a293-bf0a1d24e8e1
-- title:
--   Proof of Theorem 1, p.ec9 — one $\lambda$-column per grid cell turns the reduced program into (4)
-- statement:
--   Fix price levels $v_1\le\dots\le v_n$ in $[0,\bar v]$, a finite $\mathcal B\subset(0,\bar v)$, the merged grid $u_1\le\dots\le u_{n+m}$ of $\mathcal V$ and $\mathcal B$ with $u_{n+m+1}=\bar v$, and probabilities $x$ in the simplex. Then the reduced program of p.ec8 (multipliers $\lambda(p)$ for every $p\in[0,\bar v]$) and the finite linear program (4) (one multiplier vector $\lambda_{\cdot,i}$ per grid point $u_i$) have the same value for this $x$.
--
--   A multiplier feasible at the right end $u_{i+1}-$ of a grid cell is feasible for every $p$ in the cell, so $\lambda$ can be taken constant on each cell.
--
--   **Formalization Note** Both programs see the $\phi_k$ only through the left limits $\underline\phi_{k,j}$, so no assumption on the $\phi_k$ is made. Values are extended reals.
--
--   Differences from the source:
--   - generalization: the step is made under Assumption 1 with B the set of all breakpoints → no assumption on the ϕ_k, and any finite B ⊆ (0,v̄); reason: both programs depend on the ϕ_k only through the left limits; the statement specializes to the paper's
--   - generalization: k = 1, …, K → ϕ : Fin K → ℝ → ℝ with K = 0 allowed; reason: K = 0 is the set of all laws on [0,v̄]; every K ≥ 1 is included
--   - reading: incorporating all constraints and slightly reindexing provides the equivalent formulation (4) → equality of the values of the reduced program and of (4) for every fixed x in the simplex; reason: the reduction is made for fixed x; the joint equality follows by taking the supremum over x
--   - encoding: u₁ ≤ ⋯ ≤ u_{m+n} the ascending arrangement of V ∪ B, u_{n+m+1} = v̄; i ∈ [n+m+1], j ∈ [i−1] and j = i,…,n+m+1 → hypothesis IsMergedGrid v B u (u monotone, multiset of values = V + B), extended grid extGrid u v̄; 0-based j < i and i ≤ j; reason: same grid with ties kept; index shift only
--   - encoding: ϕ̲_{k,j} = lim_{v→u_j−} ϕ_k(v) → Function.leftLim (ϕ k) u_j, and ϕ_k(0) when u_j = 0; reason: lim_{v→0−} would look outside [0,v̄]; with right-continuity at 0, ϕ_k(0) gives the w = 0 constraints of (3)
--   - encoding: real optimal values, infima and suprema → EReal values (⊤ for an unbounded supremum or an empty infimum); reason: Lean convention; avoids the junk value 0 of real sSup/sInf on unbounded or empty sets
--   - encoding: π ∈ Π_n → v : Fin n → ℝ monotone with values in [0,v̄], x ∈ stdSimplex ℝ (Fin n); reason: the paper's parametrization of Π_n (p.9); x_i ∈ [0,1] follows from the simplex
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, proof of Theorem 1, p.ec9 (PDF p.43)

import Mathlib
import Definitions.Def_SimpleMenus_phiLow
import Definitions.Def_SimpleMenus_Rsum
import Definitions.Def_SimpleMenus_IsMergedGrid
import Definitions.Def_SimpleMenus_valueEC8
import Definitions.Def_SimpleMenus_value4

open MeasureTheory Set

namespace SimpleMenus

/-- **Reduction of `λ` to one column per grid cell** (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, proof of Theorem 1, p.ec9 = PDF
p.43): for fixed price levels `v_1 ≤ ⋯ ≤ v_n` in `[0, v̄]`, a finite `B ⊆ (0, v̄)`, the merged grid
`u` of `V` and `B` with `u_{n+m+1} = v̄`, and every `x` in the simplex, the intermediate program of
p.ec8 and the finite linear program (4) have the same value.

Formalization Note: values in `EReal`. No assumption on the `ϕ_k` is made: both programs see them
only through the left limits `ϕ̲_{k,j}`. -/
theorem theorem_1_lambda_reduction (vbar : ℝ) {K : ℕ} (phi : Fin K → ℝ → ℝ) (B : Finset ℝ)
    (hB : (B : Set ℝ) ⊆ Ioo 0 vbar) {n : ℕ} (v : Fin n → ℝ) (hv_mono : Monotone v)
    (hv_range : ∀ i, v i ∈ Icc 0 vbar) (u : Fin (n + B.card) → ℝ) (hu : IsMergedGrid v B u)
    (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) :
    valueEC8 vbar phi v x (extGrid u vbar) = value4 phi v x (extGrid u vbar) := by sorry

end SimpleMenus
