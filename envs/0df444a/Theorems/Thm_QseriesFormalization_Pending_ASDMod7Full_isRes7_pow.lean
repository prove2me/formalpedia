-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_ASDMod7Full_isRes7_pow
-- name    : QseriesFormalization.Pending.ASDMod7Full.isRes7_pow
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:43:32.446515+00:00
-- url     : https://prove2.me/theorems/b2b940f5-b4de-4199-8829-e59ae2d67a2e
-- title:
--   Powers multiply the mod-7 residue support
-- statement:
--   Let $R$ be a commutative ring, $r\in\mathbb{N}$, and $f\in R[[X]]$. For $t\in\mathbb{N}$ and $h\in R[[X]]$, write $S_{7}(t,h)$ for the condition $$\forall n\in\mathbb{N},\quad n\bmod 7\ne t\ \Longrightarrow\ [X^n]h=0.$$ If $S_{7}(r,f)$, then for every $m\in\mathbb{N}$, $$S_{7}\big((mr)\bmod 7,f^m\big).$$ The remainder is compared with $t$ literally: when $t\ge 7$, $S_{7}(t,h)$ forces $h=0$. For $t<7$ it is the usual residue-support condition.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter17_ASD_Mod7_Full.lean#L113-L128

import Definitions.Def_QseriesFormalization_DefMod7
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

/-!
# Chapter 17 — Full mod-7 ASD residue extraction

This file continues `Pending.Chapter17_ASD_Mod7`.  It keeps the
Atkin--Swinnerton-Dyer mod-7 dissection in terms of the already-proved section
components

* `ASD7 0`, the residue-0 component of `(q;q)_∞^3`;
* `ASD7 1`, the residue-1 component of `(q;q)_∞^3`;
* `ASD7 3`, the residue-3 component of `(q;q)_∞^3`.

After Frobenius, the denominator-cleared form of Hirschhorn §3.7 is

`partitionGenFun * expand 7 qPochInfPS = (ASD7 0 + ASD7 1 + ASD7 3)^2`

in `(ZMod 7)⟦X⟧`.  Applying the compressed `7`-section operator gives the
seven generating-function congruences, with the right-hand side still written
in section-component form.  The residue-5 section vanishes.
-/

open QseriesFormalization
open QseriesFormalization.Pending

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Hirschhorn7

theorem QseriesFormalization.Pending.ASDMod7Full.isRes7_pow {R : Type*} [CommRing R] {r : ℕ} {φ : R⟦X⟧}
    (hφ : IsRes7 r φ) :
    ∀ m, IsRes7 ((m * r) % 7) (φ ^ m)
  := by sorry
