-- Prove2me | Theorems.Thm_QseriesFormalization_PartIII_Ch14Thm116_coeff_zero_qPochAPPS_complex
-- name    : QseriesFormalization.PartIII.Ch14Thm116.coeff_zero_qPochAPPS_complex
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:14:08.778566+00:00
-- url     : https://prove2.me/theorems/462f41af-f3ef-4dfb-8f3e-d975e2c66e16
-- title:
--   The constant coefficient of $(q^r;q^m)_\infty$ is $1$
-- statement:
--   For natural numbers $r,m>0$, the formal power series $\prod_{n\ge0}(1-X^{r+mn})\in\mathbb{C}[[X]]$ (the formal arithmetic-progression product $(q^r;q^m)_\infty$) has constant coefficient $1$. This is a technical fact used for Theorem 11.6 (stated in the Chapter 14 development).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 14. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter14_Thm116.lean#L507-L522

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.ZMod.Basic

namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19
namespace QseriesFormalization.Pending.Ch16MBIProof end QseriesFormalization.Pending.Ch16MBIProof
namespace QseriesFormalization.Pending.RamanujanQuintic end QseriesFormalization.Pending.RamanujanQuintic
namespace QseriesFormalization.Pending.RamanujanQuinticJTP end QseriesFormalization.Pending.RamanujanQuinticJTP

/-!
# Chapter 14 — Chan Theorem 11.6 formal target

This file records the formal-power-series objects for the Lost Notebook
identity in Chan Theorem 11.6 and closes the reusable JTP-at-a-fifth-root
denominator collapse.  The remaining unproved bridge is isolated as a single
product identity involving the Rogers-Ramanujan `G,H` product factors below.
-/

open QseriesFormalization

open PowerSeries
open Filter
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.RamanujanQuinticJTP
open QseriesFormalization.Pending.Ch16MBIProof

/-! ## The four product-side series in Theorem 11.6 -/

/-! ## Period normalizations for a primitive fifth root -/

/-! ## Product rewrites for the §8.3 factors -/

/-! ## The JTP denominator collapse reused by Theorem 11.6 -/

/-! ## Unit bookkeeping for the reciprocal side -/

/-! ## Closing the remaining product bridge -/

theorem QseriesFormalization.PartIII.Ch14Thm116.coeff_zero_qPochAPPS_complex {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    (qPochAPPS ℂ r m).coeff 0 = 1 := by sorry
