-- Prove2me | Theorems.Thm_SimpleMenus_theorem_1_finite_lp
-- name    : SimpleMenus.theorem_1_finite_lp
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:50.7551+00:00
-- url     : https://prove2.me/theorems/0a9592a4-deb6-49a7-bfc4-c0e91e68f621
-- title:
--   Theorem 1 (Finite-LP) — robust $n$-level pricing with fixed price levels equals the finite LP (4) (corrected: constraint qualification and common closing side at breakpoints)
-- statement:
--   Let $\phi_1,\dots,\phi_K$ satisfy Assumption 1 with breakpoint set $\mathcal B=\{b_1<\dots<b_m\}\subset(0,\bar v)$, the constraint qualification, and a common closing side at every breakpoint. Fix $n\ge1$ price levels $v_1\le\dots\le v_n$ in $[0,\bar v]$, the merged grid $u_1\le\dots\le u_{m+n}$ of $\mathcal V$ and $\mathcal B$, $u_{n+m+1}=\bar v$, the left limits $\underline\phi_{k,j}=\lim_{w\to u_j-}\phi_k(w)$ and $S_j=\{l: v_l<u_j\}$. Consider the finite linear program
--
--   $$\sup_{\lambda\in\mathbb R_+^{K\times(m+n+1)},\ x\in\mathbb R^n_+,\ r\in\mathbb R_+} r\quad\text{s.t.}\quad \sum_{k=1}^K\underline\phi_{k,j}\lambda_{k,i}\le\sum_{l\in S_j}v_lx_l\ \ (j\in[i-1]),\qquad r\cdot u_i+\sum_{k=1}^K\underline\phi_{k,j}\lambda_{k,i}\le\sum_{l\in S_j}v_lx_l\ \ (j=i,\dots,n+m+1),\qquad\sum_{i=1}^nx_i=1, \tag{4}$$
--
--   for every $i\in[n+m+1]$. Then:
--
--   1. for every probability vector $x$, the competitive ratio of the mechanism that posts $v_i$ with probability $x_i$ equals the supremum of $r$ over the $(r,\lambda)$ feasible in (4) with this $x$;
--   2. the seller's $n$-level pricing problem with these price levels, $\sup_x\mathrm{CR}(v,x)$, equals the optimal value of (4).
--
--   This reduces the robust pricing problem with fixed price levels to a linear program with $n+K(n+m+1)+1$ variables; the paper's closed forms for the support, mean and quantile sets are solutions of it.
--
--   **Formalization Note** Values are extended reals; the competitive ratio ranges over the laws with positive benchmark.
--
--   Differences from the source:
--   - correction: no condition beyond Assumption 1 → ConstraintQualification: every ϕ_k is a step function, or some F₀ ∈ 𝓕 has ∫ ϕ_k dF₀ > 0 for every non-step ϕ_k; reason: the printed statement is false: K = 1, 0 < c < v̄, ϕ(w) = min(w − c, 0), V = {c}, x = 1 satisfies Assumption 1 with CR = c/v̄ but (3) and (4) have value 0, and at p ∈ (0, c] the homogenized primal is c while its dual is 0
--   - correction: no condition at the breakpoints → ClosingSide: at every b ∈ B all ϕ_k are left-continuous, or all are right-continuous; reason: the printed statement is false: ϕ₁ = 𝟙[w ≤ ω] − 1, ϕ₂ = 𝟙[w ≥ ω] − 1, V = {v₁}, 0 < v₁ < ω < v̄, x = 1 gives 𝓕 = {δ_ω} and CR = v₁/ω, but (4) and the reduced program of p.ec8 have value +∞
--   - reading: B = {b₁,…,b_m}, 0 < b₁ < ⋯ < b_m < v̄, the breakpoints of the ϕ_k under Assumption 1 → BreakpointAssumption: B ⊆ (0,v̄), each ϕ_k bounded, continuous and monotone on every open piece cut by B, continuous at 0 from the right and at v̄ from the left; reason: "0 < b₁" and "b_m < v̄" say that no ϕ_k has a breakpoint at 0 or at v̄
--   - reading: the n-level pricing problem is equivalent to (4), where x_i is the probability of price v_i and r the corresponding competitive ratio → (1) CR(v,x) = value of (4) at x for every x in the simplex, and (2) sup_x CR(v,x) = optimal value of (4); reason: "r is the corresponding competitive ratio" is the per-mechanism statement; "equivalent" is the equality of optimal values; both are stated
--   - generalization: B the set of all breakpoints of the ϕ_k → any finite B ⊆ (0,v̄) satisfying the hypotheses; reason: the set of all breakpoints is one such B, so the statement specializes to the paper's
--   - generalization: k = 1, …, K → ϕ : Fin K → ℝ → ℝ with K = 0 allowed; reason: K = 0 is the set of all laws on [0,v̄]; every K ≥ 1 is included
--   - encoding: u₁ ≤ ⋯ ≤ u_{m+n} the ascending arrangement of V ∪ B, u_{n+m+1} = v̄; i ∈ [n+m+1], j ∈ [i−1] and j = i,…,n+m+1 → hypothesis IsMergedGrid v B u (u monotone, multiset of values = V + B), extended grid extGrid u v̄; 0-based j < i and i ≤ j; reason: same grid with ties kept; index shift only
--   - encoding: ϕ̲_{k,j} = lim_{v→u_j−} ϕ_k(v) → Function.leftLim (ϕ k) u_j, and ϕ_k(0) when u_j = 0; reason: lim_{v→0−} would look outside [0,v̄]; with right-continuity at 0, ϕ_k(0) gives the w = 0 constraints of (3)
--   - encoding: real optimal values, infima and suprema → EReal values (⊤ for an unbounded supremum or an empty infimum); reason: Lean convention; avoids the junk value 0 of real sSup/sInf on unbounded or empty sets
--   - encoding: CR(π) = inf_{F∈𝓕} Rev(π,F)/Rev(OPT,F) → infimum over F ∈ 𝓕 with Rev(OPT,F) > 0; reason: a law with Rev(OPT,F) = 0 has Rev(π,F) = 0, the ratio 0/0; (EC.1) imposes nothing on it
--   - encoding: t(v) = ∫_0^v π(u)u du with π = Σ x_i δ(v − v_i) → pay v x w = Σ_{v_l ≤ w} x_l v_l; reason: closed form of the Dirac integral (p.ec8); the atom at w is included, the buyer buys at the posted price
--   - encoding: F ∈ P([0, v̄]), constraints ∫ ϕ_k dF ≥ 0 → Borel probability measure on ℝ with F([0,v̄]ᶜ) = 0, and Integrable (ϕ k) F in each constraint; reason: same laws; integrability holds for every such law when ϕ_k is bounded and piecewise monotone
--   - encoding: Rev(OPT,F) = max_{p≥0} p(1 − F(p−)) → supremum over p ∈ [0, v̄] of p·F([p,∞)); reason: F is carried by [0,v̄], so prices above v̄ earn 0; the maximum is attained and only its value is used
--   - encoding: v₁ ≤ ⋯ ≤ v_n ∈ [0,v̄], x ∈ ℝ^n_+ with Σ x_i = 1 → v monotone with values in [0,v̄]; x ∈ stdSimplex ℝ (Fin n); value4 for fixed x and value4Joint = sup over the simplex; reason: same program; the sup over x is taken last
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, Theorem 1 (Finite-LP), p.11, display (4)

import Mathlib
import Definitions.Def_SimpleMenus_pay
import Definitions.Def_SimpleMenus_rev
import Definitions.Def_SimpleMenus_opt
import Definitions.Def_SimpleMenus_ambiguitySet
import Definitions.Def_SimpleMenus_CR
import Definitions.Def_SimpleMenus_IsPiece
import Definitions.Def_SimpleMenus_ConstraintQualification
import Definitions.Def_SimpleMenus_BreakpointAssumption
import Definitions.Def_SimpleMenus_ClosingSide
import Definitions.Def_SimpleMenus_IsMergedGrid
import Definitions.Def_SimpleMenus_phiLow
import Definitions.Def_SimpleMenus_Rsum
import Definitions.Def_SimpleMenus_value4

open MeasureTheory Set

namespace SimpleMenus

/-- **Theorem 1 (Finite-LP)** (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, p.11), corrected: under Assumption 1 with breakpoint set
`B ⊆ (0, v̄)`, the constraint qualification and a common closing side at every breakpoint, for any
price levels `v_1 ≤ ⋯ ≤ v_n` in `[0, v̄]` (`n ≥ 1`) and the merged grid `u_1 ≤ ⋯ ≤ u_{n+m}` of `V`
and `B`, with `u_{n+m+1} = v̄`:
1. for every `x` in the simplex, the competitive ratio of the mechanism `(v, x)` is the value of the
   finite LP (4) with that `x` (`r` is the corresponding competitive ratio);
2. the seller's `n`-level pricing problem with these price levels, `sup_x CR(v, x)`, equals the
   optimal value of (4).

Formalization Note: values in `EReal`; `CR` ranges over the laws with `Rev(OPT, F) > 0`.
`ConstraintQualification` (CE1) and `ClosingSide` (CE2) are corrections, see their docstrings. -/
theorem theorem_1_finite_lp (vbar : ℝ) {K : ℕ} (phi : Fin K → ℝ → ℝ) (B : Finset ℝ)
    (hB : BreakpointAssumption vbar phi B) (hCS : ClosingSide phi B)
    (hCQ : ConstraintQualification vbar phi) {n : ℕ} (hn : 1 ≤ n) (v : Fin n → ℝ)
    (hv_mono : Monotone v) (hv_range : ∀ i, v i ∈ Icc 0 vbar) (u : Fin (n + B.card) → ℝ)
    (hu : IsMergedGrid v B u) :
    (∀ x ∈ stdSimplex ℝ (Fin n), CR vbar phi v x = value4 phi v x (extGrid u vbar)) ∧
    (⨆ x ∈ stdSimplex ℝ (Fin n), CR vbar phi v x) = value4Joint phi v (extGrid u vbar) := by sorry

end SimpleMenus
