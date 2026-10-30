-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_gaussianBinom_norm_le
-- name    : QseriesFormalization.PartII.Ch07.gaussianBinom_norm_le
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:20:52.147473+00:00
-- url     : https://prove2.me/theorems/ce40dc82-e68c-4b0a-b6e6-a1427cd5fae9
-- title:
--   Uniform bound $\|\binom{N-n}{n}_q\|\le(2/(1-\|q\|))^n$
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1$ and natural numbers $n,N$ with $2n\le N$,
--   $$\Big\|\binom{N-n}{n}_q\Big\|\le\Big(\frac{2}{1-\|q\|}\Big)^{n}.$$
--   The bound is uniform in $N$; combined with the Gaussian decay of $\|q\|^{n^2}$ it gives the dominating sequence for Tannery's theorem in the Chapter 7 proof of the Rogers-Ramanujan identities.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep5.lean#L94-L134

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

theorem QseriesFormalization.PartII.Ch07.gaussianBinom_norm_le (q : ℂ) (hq : ‖q‖ < 1) (n N : ℕ)
    (hN : 2 * n ≤ N) :
    ‖gaussianBinom q (N - n) n‖ ≤ (2 / (1 - ‖q‖)) ^ n := by sorry
