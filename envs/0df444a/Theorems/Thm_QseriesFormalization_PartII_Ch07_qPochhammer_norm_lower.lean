-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_qPochhammer_norm_lower
-- name    : QseriesFormalization.PartII.Ch07.qPochhammer_norm_lower
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:21:24.672328+00:00
-- url     : https://prove2.me/theorems/d6b46c6b-b005-4889-bf41-5d4f46096325
-- title:
--   Lower bound $(1-\|q\|)^n\le\|(q;q)_n\|$
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1$ and every natural number $n$,
--   $$(1-\|q\|)^n\le\|(q;q)_n\|,\qquad (q;q)_n=\prod_{j=1}^n(1-q^j).$$
--   This simple lower bound follows factor by factor from $\|1-q^j\|\ge1-\|q\|^j\ge 1-\|q\|$ and is used in Chapter 7 estimates.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep5.lean#L46-L67

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

theorem QseriesFormalization.PartII.Ch07.qPochhammer_norm_lower (q : ℂ) (hq : ‖q‖ < 1) :
    ∀ n : ℕ, (1 - ‖q‖) ^ n ≤ ‖qPochhammer q n‖
  := by sorry
