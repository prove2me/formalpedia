-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_ASDEtaProducts_asd5GProductPS_eq_asd5GSeriesPS_complex
-- name    : QseriesFormalization.Pending.ASDEtaProducts.asd5GProductPS_eq_asd5GSeriesPS_complex
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:36:03.898295+00:00
-- url     : https://prove2.me/theorems/d3d51b87-cbd0-4292-b927-95fbeb39d111
-- title:
--   Formal identity $G(q^5)=(q^5,q^{20},q^{25};q^{25})_\infty=\sum_k(-1)^kq^{(25k^2-15k)/2}$
-- statement:
--   In $\mathbb{C}[[X]]$,
--   $$\prod_{n\ge0}(1-X^{5+25n})(1-X^{20+25n})(1-X^{25+25n})=\sum_{k\in\mathbb{Z}}(-1)^kX^{(25k^2-15k)/2}.$$
--   The left side is $(q^5,q^{20},q^{25};q^{25})_\infty$ (called $G(q^5)$ in Hirschhorn's mod-25 eta-product setup) and the right side is the theta series $\sum_k(-1)^kX^{(5k^2-3k)/2}$ with $X\mapsto X^5$. It follows from the formal triple product identity at $(q,q^4,q^5;q^5)_\infty$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/ASD_EtaProducts.lean#L121-L126

import Definitions.Def_QseriesFormalization_DefQuintic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19

/-!
# ASD eta-product formal identities

This file records the modulus-25 eta-product identities obtained from the
closed mod-5 formal Jacobi triple product identities by the substitution
`X ↦ X^5`.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.ASDEtaProducts

open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

open JTPFormalPSPentagonal
open QseriesFormalization.PartIV.Ch19

/-! ## Expanding AP products -/

/-! ## Hirschhorn §3.6.5: the mod-25 F/G eta products -/

theorem QseriesFormalization.Pending.ASDEtaProducts.asd5GProductPS_eq_asd5GSeriesPS_complex :
    asd5GProductPS ℂ = asd5GSeriesPS ℂ := by sorry
