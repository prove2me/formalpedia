-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Packed_Tree_fastCheck_of_frontier
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck_of_frontier
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T21:04:18.964864+00:00
-- url     : https://prove2.me/theorems/65d25472-1376-4ef7-af09-40541b6f34bf
-- title:
--   fast Check of frontier — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall \mathit{deny}:\mathbb N,\quad \forall q:\mathbb N,\quad \forall \mathit{values}:\operatorname{RankCached.CostValues},\quad \forall \mathit{bound}:\mathbb N,\quad \forall \mathit{depth}:\mathbb N,\quad \forall t:\operatorname{RankAnnotated.Tree},\quad \bigl(\bigl(\operatorname{List.all}\bigl(\operatorname{Tree.frontier}\bigl(t, \mathit{depth}\bigr), \left(s\mapsto \operatorname{Tree.fastCheck}\bigl(\mathit{deny}, q, \mathit{values}, \mathit{bound}, s\bigr)\right)\bigr) = \mathsf{true}\bigr)\Longrightarrow \bigl(\operatorname{Tree.fastCheck}\bigl(\mathit{deny}, q, \mathit{values}, \mathit{bound}, t\bigr) = \mathsf{true}\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding fast Check of frontier step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22FastTree.lean, lines 34–49.

import Definitions.Def_Sensitivity213981Formal_Endpoint22FastTree
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
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

theorem Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck_of_frontier :
∀ (deny q : Nat) (values : Sensitivity213981Formal.ThreeBoundRankCached.CostValues) (bound depth : Nat)
  (t : Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree)
  (h :
    @Eq.{1} Bool
      (@List.all.{0} Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree
        (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.frontier t depth)
        fun (s : Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree) =>
        Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck deny q values bound s)
      Bool.true),
  @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck deny q values bound t) Bool.true := by sorry
