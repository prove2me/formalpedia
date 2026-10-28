-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankAnnotated_Tree_preparedCheck_of_dominance
-- name    : Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.preparedCheck_of_dominance
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:57:20.362981+00:00
-- url     : https://prove2.me/theorems/0a753d10-db8f-46ea-909a-8870933b253b
-- title:
--   prepared Check of dominance — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall \mathit{small}:\operatorname{Array}(\mathbb B),\quad \forall \mathit{large}:\operatorname{Array}(\mathbb B),\quad \bigl(\operatorname{RankAnnotated.MaskLe}\bigl(\mathit{small}, \mathit{large}\bigr)\Longrightarrow \forall q:\mathbb N,\quad \forall \mathit{pre}:\left(\mathbb N\to \operatorname{RankCached.PreparedValues}\right),\quad \forall x:\operatorname{RankCached.CostValues},\quad \forall y:\operatorname{RankCached.CostValues},\quad \forall a:\mathbb N,\quad \forall b:\mathbb N,\quad \bigl(\bigl(0 < b\bigr)\Longrightarrow \bigl(\operatorname{RankAnnotated.CoefficientLe}\bigl(q, x, y, a, b\bigr)\Longrightarrow \forall t:\operatorname{RankAnnotated.Tree},\quad \bigl(\bigl(\operatorname{Tree.preparedCheck}\bigl(\mathit{large}, q, \mathit{pre}, y, b, t\bigr) = \mathsf{true}\bigr)\Longrightarrow \bigl(\operatorname{Tree.preparedCheck}\bigl(\mathit{small}, q, \mathit{pre}, x, a, t\bigr) = \mathsf{true}\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding prepared Check of dominance step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankCoefficientDominance.lean, lines 93–116.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankAnnotatedTree
import Definitions.Def_Sensitivity213981Formal_RankCoefficientDominance
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

theorem Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.preparedCheck_of_dominance :
∀ (small large : Array.{0} Bool) (hm : Sensitivity213981Formal.ThreeBoundRankAnnotated.MaskLe small large) (q : Nat)
  (pre : Nat → Sensitivity213981Formal.ThreeBoundRankCached.PreparedValues)
  (x y : Sensitivity213981Formal.ThreeBoundRankCached.CostValues) (a b : Nat)
  (hb : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
  (hc : Sensitivity213981Formal.ThreeBoundRankAnnotated.CoefficientLe q x y a b)
  (t : Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree)
  (hy : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.preparedCheck large q pre y b t) Bool.true),
  @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.preparedCheck small q pre x a t) Bool.true := by sorry
