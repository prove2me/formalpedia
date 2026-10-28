-- Prove2me | Theorems.Thm_ThreeBoundOrdinaryArchive_Paley11987Verified_Sensitivity2075_tolerant_repair_cases
-- name    : ThreeBoundOrdinaryArchive.Paley11987Verified.Sensitivity2075.tolerant_repair_cases
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:38:01.464505+00:00
-- url     : https://prove2.me/theorems/5eeba2e5-8839-4388-abcf-1a3c67dd3619
-- title:
--   A single-bit repair of a tolerant row has two possible causes
-- statement:
--   Consider a tolerant row \(i\) in the recursive tournament construction, with target level \(A\), guard level \(G\), and tolerance \(q\). Suppose the row is false before a flip at child coordinate \(((j,c),a)\), and true afterwards. Then exactly the following alternatives cover the repair: the flip is in row \(i\)'s own child (\(j=i\)) and changes its unique missing target from false to true; or \(i\) has exactly \(q+1\) failed guards and the flip changes a selected outgoing guard from true to false. In the guard case,
--   \[
--   T(i,j),\qquad c=\ell(i,j).
--   \]
--   The theorem identifies the positions and child boundaries to which an upward-sensitive bit may be charged.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ArchivedOrdinaryRepair, lines 181–234; source SHA256 1dc9e9066ae1aaa070f39f899af9c64a43193aae6b976a2927e148ae06da4a2a.

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
open OAI.Paper320
namespace ThreeBoundOrdinaryArchive
end ThreeBoundOrdinaryArchive
open ThreeBoundOrdinaryArchive
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
open scoped Classical BigOperators
namespace ThreeBoundOrdinaryArchive.Sensitivity2075
end ThreeBoundOrdinaryArchive.Sensitivity2075
open ThreeBoundOrdinaryArchive.Sensitivity2075
open OAI.Paper320 Sensitivity205
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

theorem ThreeBoundOrdinaryArchive.Paley11987Verified.Sensitivity2075.tolerant_repair_cases
    (hoff : tolerantRow T label F A G q x i = false)
    (hon : tolerantRow T label F A G q (_root_.OAI.Paper320.flip x {((j,c),a)}) i = true) :
    (i ∈ tolerantTargets T label F A G q x ∧ j = i ∧
      F A (recursiveChild x j c) = false ∧
      F A (_root_.OAI.Paper320.flip (recursiveChild x j c) {a}) = true) ∨
    (i ∈ tolerantGuards T label F A G q x ∧ T.Adj i j ∧ c = label i j ∧
      F G (recursiveChild x j c) = true ∧
      F G (_root_.OAI.Paper320.flip (recursiveChild x j c) {a}) = false) := by sorry
