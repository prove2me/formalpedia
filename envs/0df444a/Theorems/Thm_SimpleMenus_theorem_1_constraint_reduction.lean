-- Prove2me | Theorems.Thm_SimpleMenus_theorem_1_constraint_reduction
-- name    : SimpleMenus.theorem_1_constraint_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:37:47.655555+00:00
-- url     : https://prove2.me/theorems/895b44cf-c12b-4e52-a93f-68f0a82cdb67
-- title:
--   Proof of Theorem 1, p.ec8 (corrected: common closing side) — Problem (3) reduces to constraints at $w\to u_j-$
-- statement:
--   Assume Assumption 1 with breakpoint set $\mathcal B\subset(0,\bar v)$ and a common closing side at every breakpoint. Fix price levels $v_1\le\dots\le v_n$ in $[0,\bar v]$, the merged grid $u_1\le\dots\le u_{n+m}$ of $\mathcal V$ and $\mathcal B$ with $u_{n+m+1}=\bar v$, and probabilities $x$ in the simplex. Then Problem (3) at $(v,x)$ has the same value as the reduced program in which the constraints indexed by $w$ are kept only at $w\to u_j-$:
--
--   $$\sup\{r\ge0:\ \exists\lambda\ge0,\ \textstyle\sum_k\underline\phi_{k,j}\lambda_k(p)\le\sum_{l\in S_j}x_lv_l\ (u_j\le p),\ r\,p+\sum_k\underline\phi_{k,j}\lambda_k(p)\le\sum_{l\in S_j}x_lv_l\ (u_j>p),\ \forall p\in[0,\bar v]\}.$$
--
--   Between grid points the payment is constant and $\sum_k\lambda_k\phi_k$ is nondecreasing, so only the left limits at the grid points can bind.
--
--   **Formalization Note** The statement is the equality of values, not the equivalence of the constraint systems at each $p$: at a left-closed breakpoint the systems differ while the values agree. Values are extended reals.
--
--   Differences from the source:
--   - correction: no condition at the breakpoints → ClosingSide: at every b ∈ B all ϕ_k are left-continuous, or all are right-continuous; reason: the printed statement is false: ϕ₁ = 𝟙[w ≤ ω] − 1, ϕ₂ = 𝟙[w ≥ ω] − 1, V = {v₁}, 0 < v₁ < ω < v̄, x = 1 gives 𝓕 = {δ_ω} and CR = v₁/ω, but (4) and the reduced program of p.ec8 have value +∞
--   - reading: B = {b₁,…,b_m}, 0 < b₁ < ⋯ < b_m < v̄, the breakpoints of the ϕ_k under Assumption 1 → BreakpointAssumption: B ⊆ (0,v̄), each ϕ_k bounded, continuous and monotone on every open piece cut by B, continuous at 0 from the right and at v̄ from the left; reason: "0 < b₁" and "b_m < v̄" say that no ϕ_k has a breakpoint at 0 or at v̄
--   - generalization: B the set of all breakpoints of the ϕ_k → any finite B ⊆ (0,v̄) satisfying the hypotheses; reason: the set of all breakpoints is one such B, so the statement specializes to the paper's
--   - generalization: k = 1, …, K → ϕ : Fin K → ℝ → ℝ with K = 0 allowed; reason: K = 0 is the set of all laws on [0,v̄]; every K ≥ 1 is included
--   - reading: an equivalent formulation of (3) (sup over λ, x, r) → equality of the values of (3) and of the reduced program for every fixed x in the simplex; reason: the reduction is made for fixed price levels and probabilities; the joint equality follows by taking the supremum over x; constraint systems for a single p are not equivalent at a left-closed breakpoint
--   - encoding: u₁ ≤ ⋯ ≤ u_{m+n} the ascending arrangement of V ∪ B, u_{n+m+1} = v̄; i ∈ [n+m+1], j ∈ [i−1] and j = i,…,n+m+1 → hypothesis IsMergedGrid v B u (u monotone, multiset of values = V + B), extended grid extGrid u v̄; 0-based j < i and i ≤ j; reason: same grid with ties kept; index shift only
--   - encoding: ϕ̲_{k,j} = lim_{v→u_j−} ϕ_k(v) → Function.leftLim (ϕ k) u_j, and ϕ_k(0) when u_j = 0; reason: lim_{v→0−} would look outside [0,v̄]; with right-continuity at 0, ϕ_k(0) gives the w = 0 constraints of (3)
--   - encoding: real optimal values, infima and suprema → EReal values (⊤ for an unbounded supremum or an empty infimum); reason: Lean convention; avoids the junk value 0 of real sSup/sInf on unbounded or empty sets
--   - encoding: t(v) = ∫_0^v π(u)u du with π = Σ x_i δ(v − v_i) → pay v x w = Σ_{v_l ≤ w} x_l v_l; reason: closed form of the Dirac integral (p.ec8); the atom at w is included, the buyer buys at the posted price
--   - encoding: π ∈ Π_n → v : Fin n → ℝ monotone with values in [0,v̄], x ∈ stdSimplex ℝ (Fin n); reason: the paper's parametrization of Π_n (p.9); x_i ∈ [0,1] follows from the simplex
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, proof of Theorem 1, p.ec8 (PDF p.42)

import Mathlib
import Definitions.Def_SimpleMenus_pay
import Definitions.Def_SimpleMenus_IsPiece
import Definitions.Def_SimpleMenus_BreakpointAssumption
import Definitions.Def_SimpleMenus_ClosingSide
import Definitions.Def_SimpleMenus_value3
import Definitions.Def_SimpleMenus_IsMergedGrid
import Definitions.Def_SimpleMenus_phiLow
import Definitions.Def_SimpleMenus_Rsum
import Definitions.Def_SimpleMenus_valueEC8

open MeasureTheory Set

namespace SimpleMenus

/-- **Constraint reduction to the grid left limits** (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, proof of Theorem 1, p.ec8 = PDF
p.42), with the common closing side added: under the breakpoint assumption for `B` and
`ClosingSide`, for fixed price levels `v_1 ≤ ⋯ ≤ v_n` in `[0, v̄]`, the merged grid `u` of `V` and
`B` with `u_{n+m+1} = v̄`, and every `x` in the simplex, Problem (3) at `(v, x)` and the
intermediate program of p.ec8 (constraints only at `w → u_j−`) have the same value.

Formalization Note: values in `EReal`; the statement is the equality of values, not of the
constraint systems for each `p`. `ClosingSide` is a correction (CE2, see its docstring: (3) has
value `v₁/ω`, the reduced program `+∞`). -/
theorem theorem_1_constraint_reduction (vbar : ℝ) {K : ℕ} (phi : Fin K → ℝ → ℝ)
    (B : Finset ℝ) (hB : BreakpointAssumption vbar phi B) (hCS : ClosingSide phi B) {n : ℕ}
    (v : Fin n → ℝ) (hv_mono : Monotone v) (hv_range : ∀ i, v i ∈ Icc 0 vbar)
    (u : Fin (n + B.card) → ℝ) (hu : IsMergedGrid v B u) (x : Fin n → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin n)) :
    value3 vbar phi v x = valueEC8 vbar phi v x (extGrid u vbar) := by sorry

end SimpleMenus
