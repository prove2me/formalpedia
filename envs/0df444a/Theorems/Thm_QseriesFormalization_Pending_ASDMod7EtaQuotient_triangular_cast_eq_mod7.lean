-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_ASDMod7EtaQuotient_triangular_cast_eq_mod7
-- name    : QseriesFormalization.Pending.ASDMod7EtaQuotient.triangular_cast_eq_mod7
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:42:31.349986+00:00
-- url     : https://prove2.me/theorems/db8cec30-fff6-4f3f-8735-262efe2ad7f8
-- title:
--   Triangular numbers mod 7: $k(k+1)/2\equiv4k(k+1)$
-- statement:
--   For every $k\in\mathbb{N}$, the natural number $\lfloor k(k+1)/2\rfloor$ cast to $\mathbb{Z}/7$ equals $4\,k\,(k+1)$ computed in $\mathbb{Z}/7$ (using $2^{-1}=4$ mod 7). Chapter 17 residue computation.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/ASD_Mod7_EtaQuotient.lean#L236-L254

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.ZMod.Basic

namespace QseriesFormalization.PartIV.Ch17 end QseriesFormalization.PartIV.Ch17
namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19
namespace QseriesFormalization.Pending.ASDMod7Full end QseriesFormalization.Pending.ASDMod7Full
namespace QseriesFormalization.Pending.Hirschhorn7 end QseriesFormalization.Pending.Hirschhorn7
namespace QseriesFormalization.Pending.JTPFormalPSMod7 end QseriesFormalization.Pending.JTPFormalPSMod7
namespace QseriesFormalization.Pending.JTPFormalPSPentagonal end QseriesFormalization.Pending.JTPFormalPSPentagonal

/-!
# ASD mod-7 eta-product section identifications

This file mirrors the completed mod-5 section-identification path in
`Pending.ASD_EtaProducts` for Hirschhorn's modulus-7 dissection.
-/

open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartIV.Ch17
open QseriesFormalization.Pending.Hirschhorn7
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.JTPFormalPSMod7
open QseriesFormalization.Pending.ASDMod7Full

/-! ## Integral-to-`ZMod 7` forms of the mod-7 theta product identities -/

/-! ## Coefficient matching helpers -/

theorem QseriesFormalization.Pending.ASDMod7EtaQuotient.triangular_cast_eq_mod7 (k : ℕ) :
    (((k * (k + 1) / 2 : ℕ) : ZMod 7)) =
      4 * (k : ZMod 7) * ((k : ZMod 7) + 1) := by sorry
