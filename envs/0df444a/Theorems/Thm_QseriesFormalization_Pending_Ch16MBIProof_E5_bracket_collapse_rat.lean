-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch16MBIProof_E5_bracket_collapse_rat
-- name    : QseriesFormalization.Pending.Ch16MBIProof.E5_bracket_collapse_rat
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T11:21:19.09399+00:00
-- url     : https://prove2.me/theorems/0397bf1d-3772-4a12-a149-b0fcf73aa8a6
-- title:
--   Bracket collapse: $E_0^2E_2^2-3E_0E_1^2E_2+E_1^4=5E_1^4$
-- statement:
--   Let $E_r\in\mathbb{Q}[[X]]$ be the section of $(q;q)_\infty$ consisting of terms with exponent $\equiv r\pmod5$. Then $$E_0^2E_2^2-3E_0E_1^2E_2+E_1^4=5E_1^4.$$ (Equivalently $E_0^2E_2^2-3E_0E_1^2E_2=4E_1^4$.) An algebraic step in the mod-5 dissection, Chapter 16.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 16. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter16_MBI_Proof.lean#L1169-L1185

import Definitions.Def_QseriesFormalization_DefQuintic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Pending proof work for Chan §16 / Hirschhorn §5

This file is intentionally standalone: it does not edit or import the existing
`Pending/Chapter16_MBI.lean` stub.  It develops the mod-5 section bookkeeping
needed for Ramanujan's most beautiful identity.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.Ch16MBIProof

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartI.Ch04Franklin (pentagonalSign)
open QseriesFormalization.Pending.JTPFormalPSPentagonal

theorem QseriesFormalization.Pending.Ch16MBIProof.E5_bracket_collapse_rat :
    (E5 ℚ 0)^2 * (E5 ℚ 2)^2 -
        (3 : ℚ⟦X⟧) * E5 ℚ 0 * (E5 ℚ 1)^2 * E5 ℚ 2 +
        (E5 ℚ 1)^4 =
      (5 : ℚ⟦X⟧) * (E5 ℚ 1)^4 := by sorry
