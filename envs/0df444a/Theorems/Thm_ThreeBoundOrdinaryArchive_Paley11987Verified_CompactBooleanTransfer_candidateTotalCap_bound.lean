-- Prove2me | Theorems.Thm_ThreeBoundOrdinaryArchive_Paley11987Verified_CompactBooleanTransfer_candidateTotalCap_bound
-- name    : ThreeBoundOrdinaryArchive.Paley11987Verified.CompactBooleanTransfer.candidateTotalCap_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:45:56.147862+00:00
-- url     : https://prove2.me/theorems/20390085-3c4b-4751-a361-a60cd0f3792d
-- title:
--   Label exclusions give the combined ordinary candidate cap
-- statement:
--   Let \(T\) be a labeled tournament satisfying the ordinary and marked exclusions collected in \(\operatorname{LabelCaps}\). Let \(F\) be a nested Boolean family with guard level \(g\le t\), and let \(1\le q\le8\). At any input, write \(C,G,P\) for the target candidates, guard candidates, and positive target candidates. Then
--   \[
--   |C|\le \operatorname{candidateTotalCap}(q,|G|,|P|).
--   \]
--   The defined cap combines the ordinary cutoff, the target-plus-guard cutoff, one-marker bounds, and the stronger two- and three-marker cases at small tolerances. It is the deterministic cardinality input for the ordinary transfer calculation.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ArchivedOrdinaryCaps, lines 858–950; source SHA256 e5bb0155feceabeb1058dbedb95b06b12a12e94f86ba9b7d02097cc1f2cd8a09.

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
namespace ThreeBoundOrdinaryArchive.Sensitivity205
end ThreeBoundOrdinaryArchive.Sensitivity205
namespace ThreeBoundOrdinaryArchive.Sensitivity2075
end ThreeBoundOrdinaryArchive.Sensitivity2075
namespace ThreeBoundOrdinaryArchive.SensitivityQ
end ThreeBoundOrdinaryArchive.SensitivityQ
namespace ThreeBoundOrdinaryArchive.ZL
end ThreeBoundOrdinaryArchive.ZL
namespace ThreeBoundOrdinaryArchive.ZP
end ThreeBoundOrdinaryArchive.ZP
open OAI.Paper320
namespace ThreeBoundOrdinaryArchive
end ThreeBoundOrdinaryArchive
open ThreeBoundOrdinaryArchive
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ThreeBoundOrdinaryArchive.ZT
end ThreeBoundOrdinaryArchive.ZT
open ThreeBoundOrdinaryArchive.ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem ThreeBoundOrdinaryArchive.Paley11987Verified.CompactBooleanTransfer.candidateTotalCap_bound (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hCaps : LabelCaps T label) (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ) (hq : 0 < q) (hq8 : q ≤ 8)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (tolerantTargets T label F t g q x).card ≤
      candidateTotalCap q (tolerantGuards T label F t g q x).card
        (positiveTargets T label F t g q x (by decide)).card := by sorry
