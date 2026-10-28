-- Prove2me | Theorems.Thm_ThreeBoundOrdinaryArchive_CompactTournament_augment_by_guards
-- name    : ThreeBoundOrdinaryArchive.CompactTournament.augment_by_guards
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:38:15.322385+00:00
-- url     : https://prove2.me/theorems/5d081406-ebf8-4e97-a12a-d36abd64ca70
-- title:
--   Adding guard vertices loses at most one vertex
-- statement:
--   Let \(R\) be a relation on a finite vertex type such that every two distinct vertices are related in at least one direction. Let the directed edges carry binary labels \(\ell\), and let \(C,G\) be disjoint finite vertex sets. Write \(\delta_C(i)\) for the number of outgoing label mismatches from \(i\) into \(C\) under a prescribed coloring, and \(d_G^+(i)\) for the number of outgoing neighbors in \(G\). If
--   \[
--   \delta_C(i)+d_G^+(i)\le q\quad(i\in C),\qquad
--   \delta_C(i)+d_G^+(i)\le q+1\quad(i\in G),
--   \]
--   then there is a colored set \(S\) satisfying
--   \[
--   |S|\ge |C|+|G|-1
--   \]
--   whose every vertex has at most \(q\) outgoing mismatches inside \(S\). This converts a mixed target-and-guard set into an ordinary coherent-set obstruction.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ArchivedOrdinaryCaps, lines 481–557; source SHA256 e5bb0155feceabeb1058dbedb95b06b12a12e94f86ba9b7d02097cc1f2cd8a09.

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
set_option maxHeartbeats 3000000
open scoped Classical BigOperators
namespace ThreeBoundOrdinaryArchive.CompactTournament
end ThreeBoundOrdinaryArchive.CompactTournament
open ThreeBoundOrdinaryArchive.CompactTournament
open Finset ZL
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ThreeBoundOrdinaryArchive.CompactTournament.augment_by_guards (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x)
    (ell : V × V → Fin 2) (C G : Finset V) (hdis : Disjoint C G)
    (q : ℕ) (base : V → Fin 2)
    (hC : ∀ i ∈ C, (mismatch R ell C base i).card + (outOn R G i).card ≤ q)
    (hG : ∀ i ∈ G, (mismatch R ell C base i).card + (outOn R G i).card ≤ q+1) :
    ∃ (S : Finset V) (color : V → Fin 2),
      C.card + G.card ≤ S.card + 1 ∧ OrdinaryGood R ell S q color := by sorry
