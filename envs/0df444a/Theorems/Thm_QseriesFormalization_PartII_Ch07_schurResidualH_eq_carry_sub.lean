-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_schurResidualH_eq_carry_sub
-- name    : QseriesFormalization.PartII.Ch07.schurResidualH_eq_carry_sub
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:24:03.157584+00:00
-- url     : https://prove2.me/theorems/e6df4e0a-38ea-44d3-99bb-45619919a84b
-- title:
--   Schur residual (second Rogers-Ramanujan sum) as a telescoping difference of carries
-- statement:
--   For $q\in\mathbb{C}$, $N\in\mathbb{N}$, $j\in\mathbb{Z}$, let $\mathrm{residual}_H(j)=t_{N+2}(j)-t_{N+1}(j)-q^{N+2}t_N(j)$, where $t_n(j)$ is the $j$-th summand of the theta-Gaussian sum for the second (exponent $j(5j+3)/2$) Rogers-Ramanujan identity, and let $\mathrm{carry}_H(j)$ be the explicit carry term (nonzero when $N-5j$ is even) built from zero-extended Gaussian binomials $[N+1,\cdot]_q$. Then
--   $$\mathrm{residual}_H(j)=\mathrm{carry}_H(j)-\mathrm{carry}_H(j+1).$$
--   This is the telescoping step of the recurrence for the second Rogers-Ramanujan finite sum in Chapter 7.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep1H.lean#L412-L470

import Definitions.Def_QseriesFormalization_Chapter07_RRStep1H
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 7 — Rogers-Ramanujan SECOND identity, Step 1 (H-type Schur)

Parallel to `Chapter07_RRStep1` (the G/first identity) for the H/second
identity. The H-finite-LHS is `∑_n q^{n²+n}·[N-n choose n]_q` (the `a=1`
Rogers-Ramanujan polynomial, `rrJInf q q` in the limit).

The H-Schur polynomial recurrence and RHS convention are **derived and
sanity-checked** here (same methodology that caught/corrected the G-side
`5j` floor convention), not assumed.

Target: `rrJInf q q · (q;q)_∞ = ∑'_j (-1)^j q^(j(5j+3)/2)` (h_step2).
See `docs/RR_step1_schur.md`.
-/

open QseriesFormalization
open QseriesFormalization.PartII
open QseriesFormalization.PartII.Ch07

open Filter Topology

/-! ### H-Schur recurrence (parallel to the G-side `schurSum_recurrence`) -/

/-! ### H-pentagonal exponent `j(5j+3)/2`

Fixed by `theta_sum_2_eq_jacobiSeries` (Ch04: `∑'_j (-1)^j q^(j(5j+3)/2)`),
not a guessed convention. Mechanical infrastructure parallel to the
G-side `pentExp5`. -/

/-! ### H-Schur RHS (theta-Gaussian finite form) — DERIVED + VERIFIED

Derived from the proven LHS recurrence (`rrPolyH_eq_schurSumH`) and
cross-checked against the proven `rrPolyH` oracle at `N = 0..4` (the
same sanctioned methodology that caught the G-side `2j` and `q⁵→q⁶`
errors). See `docs/RR_step1_schur.md` ("RR Step 2 — UNBLOCKED").

Key structural fact: the H form uses **top index `N+1`** (not `N`),
which is exactly what reconciles the `e`-recurrence exponent `q^{N+2}`
with the natural two-`q`-Pascal-step `q^{N+1}`. With top `N+1`, the
*same* G floor `⌊(N-5j)/2⌋` and the H pentagonal `j(5j+3)/2` close it:

`e_N = Σ_j (-1)^j q^{j(5j+3)/2} · [N+1 choose ⌊(N-5j)/2⌋]_q`. -/

/-! ### H-Schur carry-telescope (UNCONDITIONAL recurrence)

Faithful mirror of the G-side `schurResidual_eq_carry_sub` /
`schurRHSz_recurrence` (RRStep1) with top index `N+1`, pentagonal
`j(5j+3)/2`, recurrence weight `q^{N+2}`. Reuses the de-privatized
G-side `gBz_even_residual` / `gBz_odd_residual` at `M = N+1` and
`sumIcc_sub_telescope`. See `docs/RR_step1_schur.md`. -/

theorem QseriesFormalization.PartII.Ch07.schurResidualH_eq_carry_sub (q : ℂ) (N : ℕ) (j : ℤ) :
    schurResidualH q N j = schurCarryH q N j - schurCarryH q N (j + 1) := by sorry
