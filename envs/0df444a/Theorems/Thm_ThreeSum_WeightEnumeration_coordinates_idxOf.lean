-- Prove2me | Theorems.Thm_ThreeSum_WeightEnumeration_coordinates_idxOf
-- name    : ThreeSum.WeightEnumeration.coordinates_idxOf
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:44:28.54206+00:00
-- url     : https://prove2.me/theorems/89854158-f59e-47b6-9d00-52f4c8bc30e4
-- title:
--   The position of a Boolean-tagged coordinate is explicit
-- statement:
--   For $L\in\mathbb N$, enumerate the coordinates in the order
--
--   $$(0,\mathrm{false}),(0,\mathrm{true}),(1,\mathrm{false}),(1,\mathrm{true}),\ldots.$$
--
--   For every $a<L$ and Boolean tag $b$, the zero-based first-occurrence index in this list is
--
--   $$\operatorname{index}(a,b)=2a+\begin{cases}1,&b=\mathrm{true},\\0,&b=\mathrm{false}.\end{cases}$$
--
--   This identifies the coordinate order used by the two coefficient families with the digit positions in the radix representation.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/WeightEnumeration.lean#L117-L140

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
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
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments

theorem ThreeSum.WeightEnumeration.coordinates_idxOf : ∀ {L : Nat} (i : Prod.{0, 0} (Fin L) Bool),
  @Eq.{1} Nat
    (@List.idxOf.{0} (Prod.{0, 0} (Fin L) Bool)
      (@instBEqProd.{0, 0} (Fin L) Bool (@instBEqOfDecidableEq.{0} (Fin L) (instDecidableEqFin L))
        (@instBEqOfDecidableEq.{0} Bool instDecidableEqBool))
      i (ThreeSum.LocalHashMoments.coordinates L))
    (@ThreeSum.WeightEnumeration.coordinateIndex L i) := by
  sorry
