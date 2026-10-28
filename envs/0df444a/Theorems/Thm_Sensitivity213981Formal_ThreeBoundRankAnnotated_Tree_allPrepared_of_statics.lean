-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankAnnotated_Tree_allPrepared_of_statics
-- name    : Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.allPrepared_of_statics
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:55:08.435441+00:00
-- url     : https://prove2.me/theorems/2404c5e5-4ff1-4d1f-9e37-3d216786a520
-- title:
--   all Prepared of statics — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall \mathit{caps}:\operatorname{Numeric.Caps},\quad \forall \mathit{perfect}:\mathbb N,\quad \forall \mathit{codes}:\left(\mathbb N\to \mathbb N\right),\quad \forall \mathit{values}:\left(\mathbb N\to \operatorname{RankCached.ConvertedValues}\right),\quad \forall \mathit{count}:\mathbb N,\quad \forall q:\mathbb N,\quad \bigl(\bigl(q \le 3\bigr)\Longrightarrow \bigl(\forall \mathit{key}:\mathbb N,\quad \bigl(\bigl(\mathit{key} < \mathit{count}\bigr)\Longrightarrow \operatorname{RankCached.ConvertedOK}\bigl(\mathit{caps}, \mathit{perfect}, \operatorname{Endpoint22Records.staticCodeRecord}\bigl(\mathit{codes}\bigl(\mathit{key}\bigr)\bigr), \mathit{values}\bigl(\mathit{key}\bigr)\bigr)\bigr)\Longrightarrow \forall t:\operatorname{RankAnnotated.Tree},\quad \bigl(\bigl(\operatorname{Tree.checkStatics}\bigl(\mathit{codes}, \mathit{count}, t\bigr) = \mathsf{true}\bigr)\Longrightarrow \operatorname{Tree.AllPrepared}\bigl(\mathit{caps}, \mathit{perfect}, q, \operatorname{RankAnnotated.prepared}\bigl(\mathit{codes}, \mathit{values}, q\bigr), t\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding all Prepared of statics step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankAnnotatedTree.lean, lines 159–174.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankAnnotatedTree
import Definitions.Def_Sensitivity213981Formal_RankConvertedPreparation
import Definitions.Def_Sensitivity213981Formal_RankStaticPreparation
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
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

theorem Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.allPrepared_of_statics :
∀ (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat) (codes : Nat → Nat)
  (values : Nat → Sensitivity213981Formal.ThreeBoundRankCached.ConvertedValues) (count q : Nat)
  (hq : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (hkeys :
    ∀ (key : Nat),
      @LT.lt.{0} Nat instLTNat key count →
        Sensitivity213981Formal.ThreeBoundRankCached.ConvertedOK caps perfect
          (Sensitivity213981Formal.ThreeBoundEndpoint22Records.staticCodeRecord (codes key)) (values key))
  (t : Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree)
  (h : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.checkStatics codes count t) Bool.true),
  Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.AllPrepared caps perfect q
    (Sensitivity213981Formal.ThreeBoundRankAnnotated.prepared codes values q) t := by sorry
