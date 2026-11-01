-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_partition_5n_plus_4_mod_5_n_zero
-- name    : QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:39:44.430746+00:00
-- url     : https://prove2.me/theorems/c7f1942f-f1e5-4e91-86a3-15d62dd3fee9
-- title:
--   Check $p(4)\equiv0\pmod5$
-- statement:
--   For $n=0$, the partition number $p(5n+4)=p(4)$ is divisible by $5$ (indeed $p(4)=5$). This is a single numerical instance of Ramanujan's congruence $p(5n+4)\equiv0\pmod5$ (Chapter 17), not the congruence itself.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17.lean#L53-L56

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 17 — Ramanujan's partition congruences

**STATUS (2026-05-23)**: `∀ n, 5 ∣ p(5n+4)` is now **UNCONDITIONALLY** proven
(see `Pending/Chapter17_Ramanujan5Conditional.ramanujan_5_dvd_p_5n_plus_4`,
re-exported here as `ramanujan_5_dvd_p_5n_plus_4`).  The proof uses the
analytic-formal Taylor uniqueness bridge `Pending/JacobiCubeAnalyticToFormal`
to discharge the formal-PS B2 hypothesis `(qPochInfPS R)^3 = jacobiThetaPS R`.

The mod-7 and mod-11 analogs (Ramanujan's 2nd and 3rd congruences) are
**NOT** discharged unconditionally — they need η-quotient identities
(Chan §17.2/17.3) substantially more involved than the mod-5 case.
-/

open QseriesFormalization

open QseriesFormalization.Ch01 (partitionCount)

/-! ## Chapter-main: UNCONDITIONAL Ramanujan's first congruence (Ch17 §17.1)

The unconditional theorem `ramanujan_5_dvd_p_5n_plus_4 : ∀ n, 5 ∣ p(5n+4)`
lives in `Pending/Chapter17_Ramanujan5Conditional.lean` under the SAME
namespace `QseriesFormalization.PartIV.Ch17`, so it's directly accessible
as `QseriesFormalization.PartIV.Ch17.ramanujan_5_dvd_p_5n_plus_4` once
that file is imported (which it is, transitively, via the imports above). -/

/-! ## Chapter-main: conditional general Ramanujan congruences (Ch17) -/

theorem QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_zero :
    partitionCount (5 * 0 + 4) % 5 = 0 := by sorry
