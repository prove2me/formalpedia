-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_ASDMod5_coeff_qPochInfPS_pow_four_at_5n_plus_4_eq_zero
-- name    : QseriesFormalization.Pending.ASDMod5.coeff_qPochInfPS_pow_four_at_5n_plus_4_eq_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:39:29.249328+00:00
-- url     : https://prove2.me/theorems/c6f74660-2e6a-4e70-90c4-dfe5ee591c8a
-- title:
--   The $q^{5n+4}$ coefficient of $(q;q)_\infty^4$ vanishes mod $5$
-- statement:
--   For every $n\in\mathbb{N}$, in $(\mathbb{Z}/5)[[X]]$, $$[X^{5n+4}]\,(q;q)_\infty^4=0.$$ This residue-4 vanishing, obtained from the mod-5 dissection, is what yields Ramanujan's congruence $p(5n+4)\equiv0\pmod5$. Chapter 17.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter17_ASD_Mod5.lean#L172 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

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

namespace QseriesFormalization.PartI.Ch04Franklin end QseriesFormalization.PartI.Ch04Franklin
namespace QseriesFormalization.PartIV.Ch17 end QseriesFormalization.PartIV.Ch17

/-!
# Chapter 17 — Atkin-Swinnerton-Dyer congruences mod 5

This file records the mod-5 dissection used in Hirschhorn §3.6.
In `(ZMod 5)⟦X⟧`, Jacobi's cube identity shows that `(q;q)_∞^3`
has only residue `0` and residue `1` terms modulo `5`: triangular
exponents have residues `{0,1,3}`, but the `3` residue occurs exactly
when the Jacobi coefficient `2k+1` is zero in `ZMod 5`.
-/

open QseriesFormalization

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartIV.Ch17
open QseriesFormalization.PartI.Ch04Franklin

theorem QseriesFormalization.Pending.ASDMod5.coeff_qPochInfPS_pow_four_at_5n_plus_4_eq_zero (n : ℕ) :
    ((qPochInfPS (ZMod 5)) ^ 4).coeff (5 * n + 4) = 0 := by sorry
