-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_OAI_Paper320_Tournament_card_internalEdges
-- name    : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.card_internalEdges
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:38:01.297991+00:00
-- url     : https://prove2.me/theorems/25923d32-2f6a-499a-b327-4dadf86bf3d7
-- title:
--   A tournament has one internal edge per unordered vertex pair
-- statement:
--   Let \(T\) be a tournament on \(\operatorname{Fin}(k)\), and let \(I\) be a finite set of its vertices. If \(E_T(I)\) is the set of directed edges with both endpoints in \(I\), then
--   \[
--   |E_T(I)|=\binom{|I|}{2}.
--   \]
--   This identity supplies the exact edge count in the tournament budget arguments.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArchivedOrdinaryCaps.lean, lines 300–326.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Data.Fintype.Powerset
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

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.card_internalEdges :
∀ {k : Nat} (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k) (I : Finset.{0} (Fin k)),
  @Eq.{1} Nat
    (@Finset.card.{0} (Prod.{0, 0} (Fin k) (Fin k))
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.internalEdges k T I))
    (Nat.choose (@Finset.card.{0} (Fin k) I) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by sorry
