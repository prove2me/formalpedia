-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_rogersRamanujan_second
-- name    : QseriesFormalization.PartII.Ch07.rogersRamanujan_second
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:22:49.445834+00:00
-- url     : https://prove2.me/theorems/67e6b5ef-0667-4c77-bd55-430b225ebf98
-- title:
--   The second Rogers-Ramanujan identity
-- statement:
--   For $q\in\mathbb{C}$ with $0<|q|<1$,
--   $$\Big(\sum_{n\ge0}\frac{q^{n^2+n}}{(q;q)_n}\Big)\cdot\prod_{n\ge0}(1-q^{5n+2})\cdot\prod_{n\ge0}(1-q^{5n+3})=1,$$
--   that is, $\sum_{n\ge0}q^{n^2+n}/(q;q)_n=1/\big((q^2;q^5)_\infty(q^3;q^5)_\infty\big)$, where $(q;q)_n=\prod_{j=1}^n(1-q^j)$. This is the second Rogers-Ramanujan identity of Chapter 7, proved analogously to the first.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep5H.lean#L294-L344

import Definitions.Def_QseriesFormalization_Chapter07
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

theorem QseriesFormalization.PartII.Ch07.rogersRamanujan_second (q : ℂ) (hq : ‖q‖ < 1) (hq_ne : q ≠ 0) :
    rrJInf q q * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 2 n)
      * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 3 n) = 1 := by sorry
