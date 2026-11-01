-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_ASDMod5Full_isRes5_mul
-- name    : QseriesFormalization.Pending.ASDMod5Full.isRes5_mul
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:37:47.977596+00:00
-- url     : https://prove2.me/theorems/82e96466-21c6-43db-90e8-e23f82ebbfa1
-- title:
--   Residue supports mod 5 add under multiplication
-- statement:
--   Let $R$ be a commutative ring, $r,s\in\mathbb{N}$, and $f,g\in R[[X]]$. For $t\in\mathbb{N}$ and $h\in R[[X]]$, write $S_{5}(t,h)$ for the condition $$\forall n\in\mathbb{N},\quad n\bmod 5\ne t\ \Longrightarrow\ [X^n]h=0.$$ If $S_{5}(r,f)$ and $S_{5}(s,g)$, then $$S_{5}\big((r+s)\bmod 5,fg\big).$$ The remainder is compared with $t$ literally: when $t\ge 5$, $S_{5}(t,h)$ forces $h=0$. For $t<5$ it is the usual residue-support condition.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter17_ASD_Mod5_Full.lean#L106 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_Pending_Chapter17_ASD_Mod5
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

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.ASDMod5

theorem QseriesFormalization.Pending.ASDMod5Full.isRes5_mul {R : Type*} [CommRing R] {r s : ℕ} {φ ψ : R⟦X⟧}
    (hφ : IsRes5 r φ) (hψ : IsRes5 s ψ) :
    IsRes5 ((r + s) % 5) (φ * ψ) := by sorry
