-- Prove2me | Theorems.Thm_QseriesFormalization_Ch10TwoVar_CTxy_embedQ_mul
-- name    : QseriesFormalization.Ch10TwoVar.CTxy_embedQ_mul
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:51:29.26737+00:00
-- url     : https://prove2.me/theorems/8e589218-4609-486f-a149-3b7ba459ce56
-- title:
--   Constant-term extraction is $K$-linear: $\mathrm{CT}_{x,y}(f\cdot F)=f\cdot\mathrm{CT}_{x,y}(F)$
-- statement:
--   For $f\in K=\mathbb{Q}((Q))$ and $F$ in the two-variable Hahn series ring $S$ over $\mathbb{Q}$ (variables $Q,x,y$), the $x^0y^0$ term of $\mathrm{embedQ}(f)\cdot F$ equals $f$ times the $x^0y^0$ term of $F$. This is the $i=j=0$ case of the slicing lemma. Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_TwoVar.lean#L239 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

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

theorem QseriesFormalization.Ch10TwoVar.CTxy_embedQ_mul (f : K) (F : S) :
    CTxy (embedQ f * F) = f * CTxy F := by sorry
