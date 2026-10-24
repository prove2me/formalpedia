-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_tendsto_schurSumH_rrJInf
-- name    : QseriesFormalization.PartII.Ch07.tendsto_schurSumH_rrJInf
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:25:44.225044+00:00
-- url     : https://prove2.me/theorems/5a148d25-8b37-417f-b3cd-3c09d0477eb3
-- title:
--   Schur's finite sums for the second Rogers-Ramanujan identity converge to $J(q,q)$
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1$, the finite sums $S^{H}_N(q)=\sum_{n=0}^{N}q^{n^2+n}\binom{N-n}{n}_q$ converge as $N\to\infty$ to
--   $$J(q,q)=\sum_{n\ge0}\frac{q^{n^2+n}}{(q;q)_n}.$$
--   The proof uses Tannery's theorem with the same uniform bound as for the first identity. This is the left-hand-side limit in Step 5 of the second Rogers-Ramanujan identity (Chapter 7).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep5H.lean#L41-L101

import Definitions.Def_QseriesFormalization_Chapter07
import Definitions.Def_QseriesFormalization_Chapter07_RRStep1H
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 7 — Rogers-Ramanujan SECOND identity, Step 5 (Tannery limit, LHS)

H-type mirror of `Chapter07_RRStep5` (the G/first-identity LHS limit).
Takes the finite H-Schur LHS `schurSumH q N = ∑_{n} q^{n²+n}·[N-n choose n]_q`
(proved `= rrPolyH q N` in `Chapter07_RRStep1H`) to the limit `N → ∞`:

`schurSumH q N → rrJInf q q` (the `a=q` Rogers-Ramanujan series).

No analytic gap and **no bottom-index convention** is needed here — this is
the LHS half, a pure mirror of the proven G-side, dominated by the *same*
`gaussianBinom_norm_le` uniform bound (the extra `‖q‖^n` factor only helps).
-/

open QseriesFormalization
open QseriesFormalization.PartII
open QseriesFormalization.PartII.Ch07

open Filter Topology

theorem QseriesFormalization.PartII.Ch07.tendsto_schurSumH_rrJInf (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => schurSumH q N) atTop (𝓝 (rrJInf q q)) := by sorry
