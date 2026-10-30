-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_tendsto_gBz_center_schurBottomH
-- name    : QseriesFormalization.PartII.Ch07.tendsto_gBz_center_schurBottomH
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:25:05.330079+00:00
-- url     : https://prove2.me/theorems/d898bb5f-5618-4182-a5e6-9ce15913b4e1
-- title:
--   Central Gaussian binomial $\binom{N+1}{\lfloor(N-5j)/2\rfloor}_q\to1/(q;q)_\infty$
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1$ and a fixed integer $j$, the zero-extended Gaussian binomial $\Big[N+1,\ \lfloor (N-5j)/2\rfloor\Big]_q$ converges as $N\to\infty$ to $1\big/\prod_{n\ge1}(1-q^{n})$. That is, the near-central Gaussian coefficients tend to the reciprocal of Euler's product. This is the per-$j$ limit on the theta-series side in Step 5 of the second Rogers-Ramanujan identity (Chapter 7).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep5H.lean#L129-L179

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

/-! ### RR Step 5 (H) RHS — ℤ-Tannery (mirror of G-side, top index `N+1`)

`schurRHSH q N = Σ_j (-1)^j q^{pentExp5H j} gBz q (N+1) (schurBottomH N j)`.
The per-`j` central limit `[N+1 choose ⌊(N-5j)/2⌋]_q → 1/(q;q)_∞` is the
same `1/E` as the G-side (TOP `N+1` vs `N` gives the same limit since
`(q;q)_{N+1} → E` too). -/

theorem QseriesFormalization.PartII.Ch07.tendsto_gBz_center_schurBottomH (q : ℂ) (hq : ‖q‖ < 1) (j : ℤ) :
    Tendsto (fun N : ℕ => gBz q (N + 1) (schurBottomH N j)) atTop
      (𝓝 (1 / PartI.Ch04.eulerPentagonalInfiniteProduct q)) := by sorry
