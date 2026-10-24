-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch13DeepIdentity_eq1237_expanded_ratio
-- name    : QseriesFormalization.Pending.Ch13DeepIdentity.eq1237_expanded_ratio
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T11:04:31.248421+00:00
-- url     : https://prove2.me/theorems/12582f9a-8c66-4ce7-8db2-413906d22a15
-- title:
--   Expanded ratio: $F^6v^5=X^5W^6\,C\,A(v)\,B(v)$ with $C=1-v-v^2$
-- statement:
--   In $\mathbb{Q}[[X]]$ let $F=(q^5;q^5)_\infty$, $W=(q^{25};q^{25})_\infty$, $v=X\cdot r(X^5)$, $C=1-v-v^2$, $A(v)=1-2v+4v^2-3v^3+v^4$ and $B(v)=1+3v+4v^2+2v^3+v^4$. Then $$F^6\,v^5=X^5\,W^6\,C\,A(v)\,B(v).$$ An intermediate identity in the proof of Chan's Theorem 11.5 (Chapter 13).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 13. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter13_DeepIdentity.lean#L288-L371

import Definitions.Def_QseriesFormalization_Pending_Chapter13_RRCF_RForm
import Definitions.Def_QseriesFormalization_Pending_Chapter13_Watson_Algebraic
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

theorem QseriesFormalization.Pending.Ch13DeepIdentity.eq1237_expanded_ratio :
    let F : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
    let W : ℚ⟦X⟧ := PowerSeries.expand 25 (by decide) (qPochInfPS ℚ)
    let C : ℚ⟦X⟧ := 1 - rrcf_v - rrcf_v ^ 2
    let A : ℚ⟦X⟧ :=
      QseriesFormalization.Pending.WatsonAlgebraic.A rrcf_v
    let B : ℚ⟦X⟧ :=
      QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v
    F ^ 6 * rrcf_v ^ 5 = PowerSeries.X ^ 5 * W ^ 6 * C * A * B := by sorry
