-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch16MBIProof_isRes5_natCast_mul
-- name    : QseriesFormalization.Pending.Ch16MBIProof.isRes5_natCast_mul
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T11:23:31.623813+00:00
-- url     : https://prove2.me/theorems/a0711eb2-ad2b-4f3c-94d5-c387292372c9
-- title:
--   Multiplying by a constant preserves being supported on one residue class mod 5
-- statement:
--   Let $R$ be a commutative ring, $c,r\in\mathbb{N}$, and $f\in R[[X]]$. For $t\in\mathbb{N}$ and $h\in R[[X]]$, write $S_{5}(t,h)$ for the condition $$\forall n\in\mathbb{N},\quad n\bmod 5\ne t\ \Longrightarrow\ [X^n]h=0.$$ If $S_{5}(r,f)$, then $S_{5}(r,cf)$, where $c$ is mapped into $R$ as a constant. The remainder is compared with $t$ literally: when $t\ge 5$, $S_{5}(t,h)$ forces $h=0$. For $t<5$ it is the usual residue-support condition.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 16. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter16_MBI_Proof.lean#L126 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefQuintic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Pending proof work for Chan §16 / Hirschhorn §5

This file is intentionally standalone: it does not edit or import the existing
`Pending/Chapter16_MBI.lean` stub.  It develops the mod-5 section bookkeeping
needed for Ramanujan's most beautiful identity.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.Ch16MBIProof

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartI.Ch04Franklin (pentagonalSign)
open QseriesFormalization.Pending.JTPFormalPSPentagonal

theorem QseriesFormalization.Pending.Ch16MBIProof.isRes5_natCast_mul {R : Type*} [CommRing R] (c r : ℕ) {φ : R⟦X⟧}
    (hφ : IsRes5 r φ) :
    IsRes5 r ((c : R⟦X⟧) * φ) := by sorry
