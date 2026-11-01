-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_ASDMod5Full_partitionGenFun_mul_D5_sq_eq_S5_cube
-- name    : QseriesFormalization.Pending.ASDMod5Full.partitionGenFun_mul_D5_sq_eq_S5_cube
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:38:31.401997+00:00
-- url     : https://prove2.me/theorems/16c71e9c-8106-47b9-a1c0-b571aeee7c6b
-- title:
--   Denominator-cleared identity mod 5: $P\cdot Q(X^5)^2=(A_0+A_1)^3$
-- statement:
--   In $(\mathbb{Z}/5)[[X]]$ let $P$ be the partition generating function (`partitionGenFun`), $Q=(q;q)_\infty$ and $D=Q(X^5)$ (`PowerSeries.expand`), and $S=A_0+A_1$ where $A_r$ are the residue-$r$ mod 5 components of $Q^3$. Then
--   $$P\cdot D^2=S^3.$$
--   A denominator-cleared form of the Hirschhorn identity of Chapter 17's mod 5 proof.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter17_ASD_Mod5_Full.lean#L75-L84

import Definitions.Def_QseriesFormalization_Pending_Chapter17_ASD_Mod5_Full
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 17 — Full mod-5 ASD residue extraction

This file continues `Pending.Chapter17_ASD_Mod5`.  It keeps the
Atkin--Swinnerton-Dyer mod-5 dissection in terms of the already-proved section
components

* `A 0`, the residue-0 component of `(q;q)_∞^3`;
* `A 1`, the residue-1 component of `(q;q)_∞^3`.

After Frobenius, the denominator-cleared form of Hirschhorn §3.6 is

`partitionGenFun * (expand 5 qPochInfPS)^2 = (A 0 + A 1)^3`

in `(ZMod 5)⟦X⟧`.  Applying the compressed `5`-section operator gives the five
generating-function congruences, with the right-hand side still written in
section-component form.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.ASDMod5Full

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.ASDMod5

theorem QseriesFormalization.Pending.ASDMod5Full.partitionGenFun_mul_D5_sq_eq_S5_cube :
    P5 * D5 ^ 2 = S5 ^ 3 := by sorry
