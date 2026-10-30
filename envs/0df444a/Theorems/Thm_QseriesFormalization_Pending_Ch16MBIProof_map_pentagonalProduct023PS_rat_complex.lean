-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch16MBIProof_map_pentagonalProduct023PS_rat_complex
-- name    : QseriesFormalization.Pending.Ch16MBIProof.map_pentagonalProduct023PS_rat_complex
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T11:24:18.49604+00:00
-- url     : https://prove2.me/theorems/4dfb5efa-ec24-40e3-8c42-ceafa5f96c2f
-- title:
--   The product $(q^2,q^3,q^5;q^5)_\infty$ commutes with $\mathbb{Q}\to\mathbb{C}$
-- statement:
--   Applying the inclusion $\mathbb{Q}\to\mathbb{C}$ coefficientwise to the formal product $(q^2;q^5)_\infty(q^3;q^5)_\infty(q^5;q^5)_\infty\in\mathbb{Q}[[X]]$ gives the same formal product over $\mathbb{C}$. This naturality lemma transfers identities between $\mathbb{Q}$ and $\mathbb{C}$ (Chapter 16, pending).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 16. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter16_MBI_Proof.lean#L1846-L1860

import Definitions.Def_QseriesFormalization_Chapter05_Franklin
import Definitions.Def_QseriesFormalization_DefCoreQSeries
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

namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19

/-!
# Pending proof work for Chan §16 / Hirschhorn §5

This file is intentionally standalone: it does not edit or import the existing
`Pending/Chapter16_MBI.lean` stub.  It develops the mod-5 section bookkeeping
needed for Ramanujan's most beautiful identity.
-/

open QseriesFormalization
open QseriesFormalization.Pending

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartI.Ch04Franklin (pentagonalSign)
open QseriesFormalization.Pending.JTPFormalPSPentagonal

/-! ## JTP-product reduction of the remaining denominator identity -/

theorem QseriesFormalization.Pending.Ch16MBIProof.map_pentagonalProduct023PS_rat_complex :
    PowerSeries.map (algebraMap ℚ ℂ) (pentagonalProduct023PS ℚ) =
      pentagonalProduct023PS ℂ := by sorry
