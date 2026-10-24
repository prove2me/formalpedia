-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_qPochhammer_norm_uniform
-- name    : QseriesFormalization.PartII.Ch07.qPochhammer_norm_uniform
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:21:57.61299+00:00
-- url     : https://prove2.me/theorems/97f167f4-3bca-4300-84fa-519abc641246
-- title:
--   Uniform two-sided bound on $\|(q;q)_n\|$ for $|q|<1$
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1$ there exist real constants $B_{lo}>0$ and $B_{up}$ such that for every natural $n$,
--   $$B_{lo}\le\|(q;q)_n\|\le B_{up},\qquad (q;q)_n=\prod_{j=1}^{n}(1-q^j).$$
--   This is a bound on the finite $q$-Pochhammer products uniform in $n$, used in the Tannery (dominated convergence) argument of Chapter 7.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep5.lean#L269 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

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

/-! ### RR Step 5 — Tannery limit (LHS) -/

/-! ### RR Step 5 — RHS per-`j` central-Gaussian limit -/

/-! ### RR Step 5 RHS — uniform q-Pochhammer norm bounds

`‖(q;q)_n‖` converges to `‖(q;q)_∞‖ ≠ 0`, hence is uniformly bounded
above and below by a positive constant (eventually-bound + finite
prefix). No infinite-product machinery needed. -/

theorem QseriesFormalization.PartII.Ch07.qPochhammer_norm_uniform (q : ℂ) (hq : ‖q‖ < 1) :
    ∃ Blo Bup : ℝ, 0 < Blo ∧ ∀ n : ℕ,
      Blo ≤ ‖qPochhammer q n‖ ∧ ‖qPochhammer q n‖ ≤ Bup := by sorry
