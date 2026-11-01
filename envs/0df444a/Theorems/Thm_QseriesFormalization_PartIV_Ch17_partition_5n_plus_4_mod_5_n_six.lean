-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_partition_5n_plus_4_mod_5_n_six
-- name    : QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_six
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:38:40.215441+00:00
-- url     : https://prove2.me/theorems/0aa06479-db63-4299-a3c7-f69734fc0637
-- title:
--   Numerical check: $p(5\cdot 6+4)\equiv 0 \pmod{5}$ (case $n=6$)
-- statement:
--   Let $p(n)$ be the number of partitions of $n$ (`partitionCount`). The statement asserts the single case $n=6$ of Ramanujan's congruence $p(5n+4)\equiv0\pmod{5}$:
--   $$p(5\cdot 6+4)=p(34)\equiv 0 \pmod{5},$$
--   stated as `partitionCount (5 * 6 + 4) % 5 = 0`; here $p(34)=12310$. This is a finite numerical check supporting the partition congruences of Chapter 17; it is not the general congruence.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_HigherCases.lean#L56-L60

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

theorem QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_six :
    partitionCount (5 * 6 + 4) % 5 = 0 := by sorry
