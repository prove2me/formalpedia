-- Prove2me | Theorems.Thm_QseriesFormalization_Ch10TwoVar_coeffXY_embedQ_mul
-- name    : QseriesFormalization.Ch10TwoVar.coeffXY_embedQ_mul
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T08:56:47.744103+00:00
-- url     : https://prove2.me/theorems/ecc6cf7e-f8fc-4f7b-9330-b839040eeafc
-- title:
--   Slicing lemma: multiplying by an $x^0y^0$ series scales each $x,y$-slice
-- statement:
--   Let $K=\mathbb{Q}((Q))$ and $S$ the ring of Hahn series in $Q,x,y$ over $\mathbb{Q}$ (with $Q$-degree ordered first). For $f\in K$, $F\in S$ and integers $i,j$,
--   $$\mathrm{coeffXY}(\mathrm{embedQ}(f)\cdot F,\,i,\,j)=f\cdot\mathrm{coeffXY}(F,\,i,\,j),$$
--   where `coeffXY` extracts the $x^iy^j$-coefficient as an element of $K$ and `embedQ` includes $K$ in $S$ as the $x^0y^0$ part. A technical slicing lemma in the two-variable setup of Chapter 10 (tenth-order mock theta function identities).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_TwoVar.lean#L325 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_Pending_Chapter10_TwoVar
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Summable

open scoped Classical
open Set

open QseriesFormalization
open QseriesFormalization.Ch10TwoVar

/-! ## Layer A — the q-first lexicographic Hahn kernel -/

/-! ### The q-slice `coeffXY` -/

/-! ### The Q-embedding `embedQ : K →+* S` -/

theorem QseriesFormalization.Ch10TwoVar.coeffXY_embedQ_mul (f : K) (F : S) (i j : ℤ) :
    coeffXY (embedQ f * F) i j = f * coeffXY F i j := by sorry
