-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_tendsto_schurSum_rrJInf
-- name    : QseriesFormalization.PartII.Ch07.tendsto_schurSum_rrJInf
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:25:52.315177+00:00
-- url     : https://prove2.me/theorems/1d033484-9871-46eb-8baf-587102833fc5
-- title:
--   Schur's finite sums converge to the Rogers-Ramanujan series $J(1,q)$
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1$, Schur's finite sums $S_N(q)=\sum_{n=0}^N q^{n^2}\binom{N-n}{n}_q$ converge as $N\to\infty$ to the Rogers-Ramanujan series
--   $$J(1,q)=\sum_{n\ge0}\frac{q^{n^2}}{(q;q)_n}.$$
--   The proof uses Tannery's theorem (dominated convergence for series), with the pointwise limit $\binom{N-n}{n}_q\to1/(q;q)_n$ and a uniform bound. This is Step 5 (left-hand side) in Chapter 7.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep5.lean#L138-L187

import Definitions.Def_QseriesFormalization_Chapter07
import Definitions.Def_QseriesFormalization_Chapter07_RRStep1
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
open QseriesFormalization.PartII
open QseriesFormalization.PartII.Ch07

open Filter Topology

/-! ### Uniform `q`-binomial bound (ChatGPT crude-bound strategy)

`‖gaussianBinom q (N-n) n‖ ≤ (2/(1-‖q‖))^n` for `2n ≤ N`, `‖q‖<1`,
via the `q`-Pochhammer ratio identity + per-factor norm bounds. -/

/-! ### RR Step 5 — Tannery limit (LHS) -/

theorem QseriesFormalization.PartII.Ch07.tendsto_schurSum_rrJInf (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => schurSum q N) atTop (𝓝 (rrJInf 1 q)) := by sorry
