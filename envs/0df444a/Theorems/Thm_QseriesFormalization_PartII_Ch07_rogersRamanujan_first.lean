-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_rogersRamanujan_first
-- name    : QseriesFormalization.PartII.Ch07.rogersRamanujan_first
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:22:09.224414+00:00
-- url     : https://prove2.me/theorems/2d09662d-aa30-48cc-a88c-612b3ab447a3
-- title:
--   The first Rogers-Ramanujan identity
-- statement:
--   For $q\in\mathbb{C}$ with $0<|q|<1$,
--   $$\Big(\sum_{n\ge0}\frac{q^{n^2}}{(q;q)_n}\Big)\cdot\prod_{n\ge0}(1-q^{5n+1})\cdot\prod_{n\ge0}(1-q^{5n+4})=1,$$
--   that is, $\sum_{n\ge0}q^{n^2}/(q;q)_n=1/\big((q;q^5)_\infty(q^4;q^5)_\infty\big)$, where $(q;q)_n=\prod_{j=1}^n(1-q^j)$. This is the first Rogers-Ramanujan identity, proved in Chapter 7 via Schur's polynomials and the quintuple/triple-product theta identity.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep5.lean#L454-L462

import Definitions.Def_QseriesFormalization_Chapter07
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

/-! ### RR Step 5 — RHS per-`j` central-Gaussian limit -/

/-! ### RR Step 5 RHS — uniform q-Pochhammer norm bounds

`‖(q;q)_n‖` converges to `‖(q;q)_∞‖ ≠ 0`, hence is uniformly bounded
above and below by a positive constant (eventually-bound + finite
prefix). No infinite-product machinery needed. -/

/-! ### RR Step 5 RHS — theta ℤ-summability (recipe step A)

`∑_{j:ℤ} ‖q‖^{pentExp5 j}` converges: `pentExp5 j = j(5j+1)/2 ≥ |j|`,
so each one-sided tail is dominated by the geometric `‖q‖^n`. -/

/-! ### RR Step 5 step D — final assembly (Rogers-Ramanujan first identity) -/

theorem QseriesFormalization.PartII.Ch07.rogersRamanujan_first (q : ℂ) (hq : ‖q‖ < 1) (hq_ne : q ≠ 0) :
    rrJInf 1 q * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 1 n)
      * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 4 n) = 1 := by sorry
