-- Prove2me | Theorems.Thm_QseriesFormalization_PartIII_Ch14_andrewsGarvanCrankIdentity_at_one
-- name    : QseriesFormalization.PartIII.Ch14.andrewsGarvanCrankIdentity_at_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:14:52.859206+00:00
-- url     : https://prove2.me/theorems/a2c46c75-4d64-4bca-abaf-b99a44f65c01
-- title:
--   Andrews-Garvan crank identity, specialization $z=1$
-- statement:
--   Let $R$ be a field with a Hausdorff topology making it a topological ring. At $z=1$, every partition contributes weight $1$ to the crank generating function, so this specialization of the defined identity is
--   $$\Big(\sum_{n\ge0}p(n)q^n\Big)\cdot\Big(\prod_{i\ge1}(1-q^i)\Big)^2=(q;q)_\infty.$$
--   Here $(q;q)_\infty$ is `qPochInfPS R`, defined as the inverse of the partition generating series. Only the $z=1$ specialization is asserted. The unadjusted crank distribution used in this source has a degree-one exception to the usual general-$z$ product formula.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 14. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter14_CrankGenFun.lean#L169-L175

import Definitions.Def_QseriesFormalization_Chapter14_CrankGenFun
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

/-!
# Chapter 14 - Crank generating function

This companion file gives a bounded formal-power-series layer for the
Andrews-Garvan crank identity.

Closed here:

* `crankCount m n`, the formal `M(m,n)` fiber count from the existing
  `crank : Nat.Partition n -> Int`.
* `crankGenFunEval R z`, the one-variable q-series obtained by evaluating the
  bilateral z-variable at a fixed field element `z`.
* the coefficient formula
  `coeff_n = sum_m M(m,n) z^m`, grouped over the finite crank support.
* the `z = 1` specialization: the crank series is the ordinary partition
  generating function, hence satisfies the product/inverse identity already
  proved in Chapter 19.

The full bilateral Laurent-series identity for arbitrary `z` is stated as a
Prop (`andrewsGarvanCrankIdentityStatement`) but is not proved here.
-/

open scoped BigOperators
open scoped PowerSeries.WithPiTopology

open QseriesFormalization
open QseriesFormalization.PartIII
open QseriesFormalization.PartIII.Ch14

open PowerSeries

/-! ## The coefficient side `M(m,n)` -/

/-! ## Fixed-`z` crank q-series -/

/-! ## The closed `z = 1` specialization -/

/-! ## Product-side statement for arbitrary fixed `z` -/

theorem QseriesFormalization.PartIII.Ch14.andrewsGarvanCrankIdentity_at_one
    (R : Type*) [Field R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    andrewsGarvanCrankIdentityStatement R 1 := by sorry
