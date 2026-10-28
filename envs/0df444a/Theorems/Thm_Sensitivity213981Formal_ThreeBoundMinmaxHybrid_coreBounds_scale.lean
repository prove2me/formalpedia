-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxHybrid_coreBounds_scale
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxHybrid.coreBounds_scale
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:32:25.108626+00:00
-- url     : https://prove2.me/theorems/24bc28df-d580-46df-ae66-0a3bafa8820c
-- title:
--   core Bounds scale — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall \mathit{degree}:\mathbb N,\quad \forall \mathit{pcross}:\mathbb N,\quad \forall \mathit{recipe}:\left(\{0,\ldots,n-1\}\to \operatorname{MinmaxNumeric.Entry}\right),\quad \forall v:\operatorname{FullProfile.Profile}\bigl(n\bigr),\quad \forall w:\operatorname{FullProfile.Profile}\bigl(n\bigr),\quad \bigl(\operatorname{MinmaxHybrid.CoreBounds}\bigl(\mathit{degree}, \mathit{pcross}, \mathit{recipe}, v, w\bigr)\Longrightarrow \forall c:\mathbb N,\quad \operatorname{MinmaxHybrid.CoreBounds}\bigl(\mathit{degree}, \mathit{pcross}, \mathit{recipe}, \operatorname{FullProfile.scale}\bigl(c, v\bigr), \operatorname{FullProfile.scale}\bigl(c, w\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding core Bounds scale step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxHybridTransfer.lean, lines 47–69.

import Definitions.Def_Sensitivity213981Formal_ClosureHomogeneity
import Definitions.Def_Sensitivity213981Formal_MinmaxCoreBounds
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxHybridTransfer
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
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
import Mathlib.Data.List.Sort
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxHybrid.coreBounds_scale :
∀ {n : Nat} (degree pcross : Nat) (recipe : Fin n → Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry)
  (v w : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (h : @Sensitivity213981Formal.ThreeBoundMinmaxHybrid.CoreBounds n degree pcross recipe v w) (c : Nat),
  @Sensitivity213981Formal.ThreeBoundMinmaxHybrid.CoreBounds n degree pcross recipe
    (@Sensitivity213981Formal.ThreeBoundFullProfile.scale n c v)
    (@Sensitivity213981Formal.ThreeBoundFullProfile.scale n c w) := by sorry
