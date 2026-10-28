-- Prove2me | Theorems.Thm_ThreeBoundOrdinaryArchive_ZL_markedGood_mono
-- name    : ThreeBoundOrdinaryArchive.ZL.markedGood_mono
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:38:06.502331+00:00
-- url     : https://prove2.me/theorems/0fc874c3-c487-4d99-969f-3aa0bce2bef5
-- title:
--   Marked coherence persists under restriction and budget enlargement
-- statement:
--   Fix a directed relation \(R\), binary edge labels, a coloring, and a marker set \(M\). Let \(A'\subseteq A\), \(P'\subseteq P\), and \(B\le B'\). If \(A,M,P\) satisfy the marked-coherence conditions at tolerance \(q\) with total marker mismatch budget \(B\), then
--   \[
--   \operatorname{MarkedGood}(A',M,P',q,B')
--   \]
--   holds for the same relation, labels, and coloring. The conditions bound local mismatch counts and the sum of marker mismatches. This restriction principle allows a large configuration to be reduced to the fixed sizes of a forbidden event.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ArchivedOrdinaryCaps, lines 51–78; source SHA256 e5bb0155feceabeb1058dbedb95b06b12a12e94f86ba9b7d02097cc1f2cd8a09.

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
set_option maxHeartbeats 6000000
open scoped Classical BigOperators
namespace ThreeBoundOrdinaryArchive.ZL
end ThreeBoundOrdinaryArchive.ZL
open ThreeBoundOrdinaryArchive.ZL
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ThreeBoundOrdinaryArchive.ZL.markedGood_mono (R : V → V → Prop) (ell : V × V → Fin 2)
    (A A' M P P' : Finset V) (hA : A' ⊆ A) (hP : P' ⊆ P)
    (q B B' : ℕ) (hB : B ≤ B') (color : V → Fin 2)
    (hg : MarkedGood R ell A M P q B color) :
    MarkedGood R ell A' M P' q B' color := by sorry
