-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_qPochhammer_norm_extend
-- name    : QseriesFormalization.PartII.Ch07.qPochhammer_norm_extend
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:21:24.203698+00:00
-- url     : https://prove2.me/theorems/ebff1c79-35c8-4b56-98c4-b0e6f9c19181
-- title:
--   Norm bound when extending $(q;q)_m$ by $k$ more factors
-- statement:
--   For $q\in\mathbb{C}$ with $\|q\|\le1$ and natural numbers $m,k$,
--   $$\|(q;q)_{m+k}\|\le\|(q;q)_m\|\cdot2^{k},$$
--   since each additional factor $1-q^{j}$ has norm at most $2$. This is an elementary estimate used in Chapter 7.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep5.lean#L69-L92

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 7 — Rogers-Ramanujan Step 5 (Tannery limit, LHS)

Takes the unconditional finite Schur identity `schurSum q N = schurRHS q N`
(proved in `Chapter07_RRStep1`) to the limit `N → ∞`.

LHS pointwise limit (this file, complete, no analytic gap):
`q^(n²)·[N-n choose n]_q → rrJTerm 1 q n` as `N → ∞`, from the proven
`tendsto_gaussianBinom_sub`.

The full Tannery step (dominated convergence: `schurSum q N → rrJInf 1 q`)
needs a uniform `q`-binomial bound; that analytic core is tracked in
`docs/RR_step1_schur.md` (RR Step 5 dispatch) and added once complete.
-/

open QseriesFormalization

open Filter Topology

/-! ### Uniform `q`-binomial bound (ChatGPT crude-bound strategy)

`‖gaussianBinom q (N-n) n‖ ≤ (2/(1-‖q‖))^n` for `2n ≤ N`, `‖q‖<1`,
via the `q`-Pochhammer ratio identity + per-factor norm bounds. -/

theorem QseriesFormalization.PartII.Ch07.qPochhammer_norm_extend (q : ℂ) (hq : ‖q‖ ≤ 1) (m : ℕ) :
    ∀ k : ℕ, ‖qPochhammer q (m + k)‖ ≤ ‖qPochhammer q m‖ * 2 ^ k
  := by sorry
