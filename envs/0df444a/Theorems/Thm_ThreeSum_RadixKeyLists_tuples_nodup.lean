-- Prove2me | Theorems.Thm_ThreeSum_RadixKeyLists_tuples_nodup
-- name    : ThreeSum.RadixKeyLists.tuples_nodup
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:25:58.482976+00:00
-- url     : https://prove2.me/theorems/bf4a7224-e9b9-47c5-b404-cc656d0a887e
-- title:
--   Cartesian tuple enumeration has no duplicate records
-- statement:
--   Let $B$ be a list of elements of any type, with no repeated element. Define $\mathcal T_0(B)=[[]]$ and construct $\mathcal T_{j+1}(B)$ by prepending each element of $B$, in order, to every tuple in $\mathcal T_j(B)$. For every $j\in\mathbb N$,
--
--   $$
--   \operatorname{Nodup}(B)\quad\Longrightarrow\quad\operatorname{Nodup}(\mathcal T_j(B)).
--   $$
--
--   This preserves distinct record sequences before they are mapped to positional integer keys, even if that later key map has collisions.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/RadixKeyLists.lean#L78-L90

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.RadixKeyLists.tuples_nodup : ∀ {α : Type u_1} (base : List.{u_1} α) (hbase : @List.Nodup.{u_1} α base) (j : Nat),
  @List.Nodup.{u_1} (List.{u_1} α) (@ThreeSum.RadixKeyLists.tuples.{u_1} α base j) := by
  sorry
