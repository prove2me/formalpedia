-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_partition_7n_plus_5_mod_7_n_six
-- name    : QseriesFormalization.PartIV.Ch17.partition_7n_plus_5_mod_7_n_six
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:41:07.848729+00:00
-- url     : https://prove2.me/theorems/accc7a50-ef2b-4ffb-b402-93ad9866c7da
-- title:
--   Numerical check: $p(7\cdot 6+5)\equiv 0 \pmod{7}$ (case $n=6$)
-- statement:
--   Let $p(n)$ be the number of partitions of $n$ (`partitionCount`). The statement asserts the single case $n=6$ of Ramanujan's congruence $p(7n+5)\equiv0\pmod{7}$:
--   $$p(7\cdot 6+5)=p(47)\equiv 0 \pmod{7},$$
--   stated as `partitionCount (7 * 6 + 5) % 7 = 0`; here $p(47)=124754$. This is a finite numerical check supporting the partition congruences of Chapter 17; it is not the general congruence.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_HigherCases.lean#L118-L122

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
# Chapter 17 — Ramanujan congruences at higher `n`

Companion file to `Chapter17.lean`.  With `partitionCount 12..22` now
proved unconditionally (`Chapter01_PartitionCount{12..22}.lean`), we can
extend Chan §17's verified `5∣p(5n+4)`, `7∣p(7n+5)`, `11∣p(11n+6)`
congruences from the n=0 and n=1 cases (in `Chapter17.lean`) to several
larger `n`:

| Family | New `n` | Witness |
|--------|---------|---------|
| 5 ∣ p(5n+4) | n=2 | p(14) = 135 = 27·5 |
| 5 ∣ p(5n+4) | n=3 | p(19) = 490 = 98·5 |
| 7 ∣ p(7n+5) | n=1 | p(12) = 77 = 11·7 |
| 7 ∣ p(7n+5) | n=2 | p(19) = 490 = 70·7 |
| 11 ∣ p(11n+6) | n=1 | p(17) = 297 = 27·11 |

Each is proved unconditionally by `simp` on the relevant
`partitionCount_N` value plus `decide` on the divisibility. -/

open QseriesFormalization

open QseriesFormalization.Ch01 (partitionCount)

/-! ## Mod-5 family: `5 ∣ p(5n+4)` -/

/-! ## Mod-7 family: `7 ∣ p(7n+5)` -/

theorem QseriesFormalization.PartIV.Ch17.partition_7n_plus_5_mod_7_n_six :
    partitionCount (7 * 6 + 5) % 7 = 0 := by sorry
