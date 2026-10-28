-- Prove2me | Theorems.Thm_ThreeBoundOrdinaryArchive_ZT_source_exclusion_source_bound
-- name    : ThreeBoundOrdinaryArchive.ZT.source_exclusion_source_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:38:32.667809+00:00
-- url     : https://prove2.me/theorems/23331caa-2e49-4f05-b0e7-2daf3444fdee
-- title:
--   Excluding source events bounds coherent sets with a source
-- statement:
--   Let \(T\) be a binary-labeled tournament, and let \(a\) be a natural number. Suppose every source event with an \(a\)-vertex out-neighbor set is absent. If a colored set \(S\) has a source \(s\in S\) and every internal outgoing edge has the color of its head, then
--   \[
--   |S|<a+1.
--   \]
--   The conclusion is the source bound needed for zero-tolerance repair candidates.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ArchivedExclusionBridge, lines 132–168; source SHA256 39791351f29a237eb7cc87fdc561a0b53aa8335c8d813157bbe79e726eb9c567.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Sensitivity213303_ArchivedOrdinaryDefinitions

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundOrdinaryArchive.OAI.Paper320
end ThreeBoundOrdinaryArchive.OAI.Paper320
namespace ThreeBoundOrdinaryArchive.SensitivityQ
end ThreeBoundOrdinaryArchive.SensitivityQ
namespace ThreeBoundOrdinaryArchive.ZL
end ThreeBoundOrdinaryArchive.ZL
open OAI.Paper320
namespace ThreeBoundOrdinaryArchive
end ThreeBoundOrdinaryArchive
open ThreeBoundOrdinaryArchive
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
open scoped Classical BigOperators
namespace ThreeBoundOrdinaryArchive.ZT
end ThreeBoundOrdinaryArchive.ZT
open ThreeBoundOrdinaryArchive.ZT
open OAI.Paper320 ZL SensitivityQ
variable {k : ℕ}

theorem ThreeBoundOrdinaryArchive.ZT.source_exclusion_source_bound (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (a : ℕ)
    (h : ∀ I : SourceIndex T.Adj a,
      ¬ (sourceFamily T.Adj a).bad I (fun e => label e.1 e.2)) :
    SensitivitySourceZero.SourceBound T label (a+1) := by sorry
