-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_ramanujan_5_dvd_p_5n_plus_4
-- name    : QseriesFormalization.PartIV.Ch17.ramanujan_5_dvd_p_5n_plus_4
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:44:19.404376+00:00
-- url     : https://prove2.me/theorems/0bdd9d68-8923-42af-be31-d4937d30f3ad
-- title:
--   Ramanujan's congruence: $5\mid p(5n+4)$ for all $n$
-- statement:
--   For every natural number $n$, the number of partitions $p(5n+4)$ is divisible by $5$:
--   $$p(5n+4)\equiv0\pmod 5.$$
--   Here $p$ is `partitionCount`. This is Ramanujan's first partition congruence, the main result of Chapter 17's mod 5 treatment.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter17_Ramanujan5Conditional.lean#L116-L127

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19

/-!
# Chapter 17 — Ramanujan's `5 ∣ p(5n+4)` conditional on B2 (Jacobi triple product formal-PS)

This file assembles the full unconditional proof of Ramanujan's first
congruence `∀ n, 5 ∣ p(5n+4)`, **conditional on the single deep open
theorem B2**:

  `(qPochInfPS R)^3 = jacobiThetaPS R`        (formal power series version)

Once B2 is closed (which requires Sylvester's combinatorial bijection
or an analytic ↔ formal Taylor uniqueness bridge), the unconditional
Ramanujan congruence drops out as a corollary of:

  - `Chapter17_SectionBridge.ramanujan_congruence_from_section_vanishing`
  - `Chapter17_Mod5ResidueAnalysis.triangular_plus_pentagonal_ne_four`
  - `Chapter19.ramanujan_key_identity`
  - `Chapter19_Section5.section_kr_X_pow_mul_expand` / `_expand_eq_zero`

This conditional theorem is currently the cleanest summary of the
session's real-proof investment.  No `sorry` — only `B2` as an explicit
quantified hypothesis.
-/

open QseriesFormalization

open QseriesFormalization.PartIV.Ch19

theorem QseriesFormalization.PartIV.Ch17.ramanujan_5_dvd_p_5n_plus_4 :
    ∀ n, 5 ∣ QseriesFormalization.Ch01.partitionCount (5 * n + 4) := by sorry
