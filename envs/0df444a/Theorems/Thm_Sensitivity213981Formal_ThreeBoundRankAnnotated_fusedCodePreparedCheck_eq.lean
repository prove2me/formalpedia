-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankAnnotated_fusedCodePreparedCheck_eq
-- name    : Sensitivity213981Formal.ThreeBoundRankAnnotated.fusedCodePreparedCheck_eq
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:53:50.843394+00:00
-- url     : https://prove2.me/theorems/1e310ba9-4510-4edb-99eb-2c547cc4c221
-- title:
--   fused Code Prepared Check eq — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall q:\mathbb N,\quad \forall p:\operatorname{RankCached.PreparedValues},\quad \forall \mathit{values}:\operatorname{RankCached.CostValues},\quad \forall \mathit{bound}:\mathbb N,\quad \forall \mathit{code}:\mathbb N,\quad \bigl(\operatorname{RankAnnotated.fusedCodePreparedCheck}\bigl(q, p, \mathit{values}, \mathit{bound}, \mathit{code}\bigr) = \operatorname{RankAnnotated.codePreparedCheck}\bigl(q, p, \mathit{values}, \mathit{bound}, \mathit{code}\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding fused Code Prepared Check eq step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22FusedPrepared.lean, lines 28–56.

import Definitions.Def_Sensitivity213981Formal_Endpoint22FusedPrepared
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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

theorem Sensitivity213981Formal.ThreeBoundRankAnnotated.fusedCodePreparedCheck_eq :
∀ (q : Nat) (p : Sensitivity213981Formal.ThreeBoundRankCached.PreparedValues)
  (values : Sensitivity213981Formal.ThreeBoundRankCached.CostValues) (bound code : Nat),
  @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundRankAnnotated.fusedCodePreparedCheck q p values bound code)
    (Sensitivity213981Formal.ThreeBoundRankAnnotated.codePreparedCheck q p values bound code) := by sorry
