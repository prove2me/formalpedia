-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_ASDMod7Full_section_kr_mul_expand
-- name    : QseriesFormalization.Pending.ASDMod7Full.section_kr_mul_expand
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:44:07.296296+00:00
-- url     : https://prove2.me/theorems/1b03ac4f-2cbc-4e2e-84f3-4636e943674e
-- title:
--   Section of a product with an expanded series: $\mathrm{section}_{p,r}(f\cdot g(X^p))=\mathrm{section}_{p,r}(f)\cdot g$
-- statement:
--   Let $R$ be a commutative ring, $p\ne0$, $r<p$ and $f,g\in R[[X]]$. With $\mathrm{section}_{p,r}\varphi=\sum_n[X^{pn+r}]\varphi\,X^n$ (`section_kr`) and $g(X^p)$ the substitution `PowerSeries.expand`, $\mathrm{section}_{p,r}(f\cdot g(X^p))=\mathrm{section}_{p,r}(f)\cdot g$. A helper in Chapter 17's mod 7 argument.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter17_ASD_Mod7_Full.lean#L32-L53

import Definitions.Def_QseriesFormalization_Chapter19_Section5
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

namespace QseriesFormalization.Pending.Hirschhorn7 end QseriesFormalization.Pending.Hirschhorn7

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

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Hirschhorn7

theorem QseriesFormalization.Pending.ASDMod7Full.section_kr_mul_expand (R : Type*) [CommRing R] (p : ℕ) (hp : p ≠ 0)
    (f g : R⟦X⟧) (r : ℕ) (hr : r < p) :
    section_kr R p r (f * PowerSeries.expand p hp g) =
      section_kr R p r f * g := by sorry
