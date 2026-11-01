-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuintic_scaleX_qPochFinitePS
-- name    : QseriesFormalization.Pending.RamanujanQuintic.scaleX_qPochFinitePS
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:49:48.415405+00:00
-- url     : https://prove2.me/theorems/383e2977-c3f2-4757-a8ca-2f48ca2b163e
-- title:
--   Rescaling of a finite $q$-Pochhammer product: $f(cX)$ for $(q;q)_N$
-- statement:
--   For a commutative ring $R$, $c\in R$ and $N\in\mathbb{N}$, in $R[[X]]$ $$\mathrm{sc}_c\Big(\prod_{k=1}^{N}(1-X^k)\Big)=\prod_{k=1}^{N}\big(1-c^{k}X^{k}\big),$$ where $\mathrm{sc}_c$ is the substitution $X\mapsto cX$. Basic formula for the quintic root-of-unity argument.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuintic.lean#L56-L61

import Definitions.Def_QseriesFormalization_DefQuintic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Ramanujan quintic cyclotomic infrastructure

This file builds a small, reusable formal-power-series layer for the
root-of-unity product route toward Hirschhorn's quintic product identity.

The results below are deliberately finite/product-local: they prove the
`X ↦ cX` power-series homomorphism API and the fifth-root finite factor
collapse.  They do not assert the infinite-product quotient or the final
`core * P5 = E^11` identity.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.RamanujanQuintic

open Finset
open PowerSeries
open scoped PowerSeries
open QseriesFormalization.PartIV.Ch19

/-! ## Scaling the variable -/

theorem QseriesFormalization.Pending.RamanujanQuintic.scaleX_qPochFinitePS {R : Type*} [CommRing R] (c : R) (N : ℕ) :
    scaleX c (qPochFinitePS R N) =
      ∏ k ∈ Finset.range N,
        ((1 : R⟦X⟧) -
          PowerSeries.C (c ^ (k + 1)) * PowerSeries.X ^ (k + 1)) := by sorry
