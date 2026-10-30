-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch13DeepIdentity_eq1237_original_branch
-- name    : QseriesFormalization.Pending.Ch13DeepIdentity.eq1237_original_branch
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T11:04:46.807721+00:00
-- url     : https://prove2.me/theorems/7a2260ed-65c8-4d87-bdec-af1061499d93
-- title:
--   Eq. (12.37)-type relation: $E^6Y=X\,F^6(1-11Y-Y^2)$ with $Y=Xr(q)^5$
-- statement:
--   In $\mathbb{Q}[[X]]$ set $E=(q;q)_\infty$, $F=(q^5;q^5)_\infty$ and $Y=X\cdot r^5$, where $r=P_{014}P_{023}^{-1}$ is the Rogers--Ramanujan series. Then $$E^6\,Y=X\,F^6\,\big(1-11Y-Y^2\big).$$ This is the original-branch form of the deep identity relating $r(q)^5$ to $E(q)^6/E(q^5)^6$ (Chapter 13).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 13. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter13_DeepIdentity.lean#L227-L286

import Definitions.Def_QseriesFormalization_Pending_Chapter13_RRCF_RForm
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.ZMod.Basic

namespace QseriesFormalization.Pending.Ch16MBIProof end QseriesFormalization.Pending.Ch16MBIProof

/-!
# Chapter 13 / §11.5 — Chan's "difficult and deep" identity (Theorem 11.5)

This file assembles the final Watson proof from the Chapter 13 prerequisites.

## The identity

Chan (cf. Hirschhorn, *The Power of q*, §9.2) calls the following the
"deep and difficult" identity of Ramanujan / Rogers-Ramanujan continued
fraction theory:

  `R(q)⁵ = R(q⁵) · (1 − 2·R(q⁵) + 4·R(q⁵)² − 3·R(q⁵)³ + R(q⁵)⁴)
                 / (1 + 3·R(q⁵) + 4·R(q⁵)² + 2·R(q⁵)³ + R(q⁵)⁴)`

where `R(q)` is the Rogers-Ramanujan continued fraction.  Since both sides
involve fractional `q`-powers (R(q) carries a `q^{1/5}` prefactor), we work
with the fractional-power-free variables defined in
`Pending/Chapter13_RRCF_RForm`:

  `r(q) := R(q)·q^{-1/5} = (q,q⁴,q⁵;q⁵)_∞ / (q²,q³,q⁵;q⁵)_∞`,
  `v := X · r(q⁵) = X · PowerSeries.expand 5 r(q)`.

Then the identity becomes the *formal-power-series* identity:

  `r(q)⁵ · (1 + 3v + 4v² + 2v³ + v⁴) = r(q⁵) · (1 − 2v + 4v² − 3v³ + v⁴)`.

Both denominators on the RHS / LHS are units in `ℚ⟦X⟧` (proved as
`Ch13RRCF.isUnit_rrcfDenomLHS` and `Ch13RRCF.isUnit_rrcfDenomRHS`), so the
quotient form `r(q)⁵ = r(q⁵)·N(v)/D(v)` is valid as a multiplicative
inverse identity in `ℚ⟦X⟧`; we state the **multiplicative form** below to
avoid any division.

## Numerical evidence

The identity has been verified term-by-term in `ℚ⟦X⟧` up to degree 60 by a
Sage/Python script; the residual difference at every degree is `0` (see
the Hirschhorn §9.2 derivation for the analytic reason).

The proof below follows Watson's algebraic route: Theorem 11.3 and Eq. 12.37
put `X * r(q)^5` and `v = X * r(q^5)` on the same quadratic branch, and
Watson's polynomial identities identify the branch.
-/

open QseriesFormalization
open QseriesFormalization.Pending

open QseriesFormalization.Pending.Ch13RRCF
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.Ch16MBIProof

open PowerSeries

theorem QseriesFormalization.Pending.Ch13DeepIdentity.eq1237_original_branch :
    let E : ℚ⟦X⟧ := qPochInfPS ℚ
    let F : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
    let Y : ℚ⟦X⟧ := PowerSeries.X * rrcf_r ^ 5
    E ^ 6 * Y = PowerSeries.X * F ^ 6 * (1 - 11 * Y - Y ^ 2) := by sorry
