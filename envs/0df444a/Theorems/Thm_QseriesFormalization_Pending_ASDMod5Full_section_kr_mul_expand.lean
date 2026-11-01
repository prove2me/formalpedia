-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_ASDMod5Full_section_kr_mul_expand
-- name    : QseriesFormalization.Pending.ASDMod5Full.section_kr_mul_expand
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:39:07.498172+00:00
-- url     : https://prove2.me/theorems/3d06e55e-a71b-49a8-84be-a360101ccdef
-- title:
--   Section of a product with an expanded series: $\mathrm{section}_{p,r}(f\cdot g(X^p))=\mathrm{section}_{p,r}(f)\cdot g$
-- statement:
--   Let $R$ be a commutative ring, $p\ne0$, $r<p$ and $f,g\in R[[X]]$. Writing $\mathrm{section}_{p,r}\varphi=\sum_n[X^{pn+r}]\varphi\,X^n$ (`section_kr`) and $g(X^p)$ for `PowerSeries.expand`,
--   $$\mathrm{section}_{p,r}\big(f\cdot g(X^p)\big)=\mathrm{section}_{p,r}(f)\cdot g.$$
--   The factor $g(X^p)$ only has exponents divisible by $p$. Chapter 17 helper.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter17_ASD_Mod5_Full.lean#L31-L52

import Definitions.Def_QseriesFormalization_Chapter19_Section5
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

namespace QseriesFormalization.Pending.ASDMod5 end QseriesFormalization.Pending.ASDMod5

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

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.ASDMod5

theorem QseriesFormalization.Pending.ASDMod5Full.section_kr_mul_expand (R : Type*) [CommRing R] (p : ℕ) (hp : p ≠ 0)
    (f g : R⟦X⟧) (r : ℕ) (hr : r < p) :
    section_kr R p r (f * PowerSeries.expand p hp g) =
      section_kr R p r f * g := by sorry
