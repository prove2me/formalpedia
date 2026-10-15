-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeOrder_tuples_getD_indices
-- name    : ThreeSum.OutputDecodeOrder.tuples_getD_indices
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:28:55.684846+00:00
-- url     : https://prove2.me/theorems/40671bdc-420e-4e5a-9de1-1260ec98841f
-- title:
--   Physical tuple indices decode as fixed-length radix digits
-- statement:
--   Let $A=[a_0,\ldots,a_{m-1}]$ be a nonempty list of elements of any type, and let $J,k\in\mathbb N$ with $k<m^J$. Enumerate all length-$J$ tuples from this list in the product order with the first coordinate outermost. Let $(d_0,\ldots,d_{J-1})$ be the length-$J$ base-$m$ digit list of $k$, with leading zeros and the last digit obtained by remainder. Then
--
--   $$
--   \operatorname{tuples}(A,J)[k]=[a_{d_0},\ldots,a_{d_{J-1}}].
--   $$
--
--   The formal lookup may use any default element; the index bounds ensure it is never needed. Repeated values in $A$ are allowed.
--
--   This ties quotient/remainder decoding to exact physical enumeration order rather than merely to the set of tuple values.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/OutputDecodeOrder.lean#L109-L128

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists

universe u_1

theorem ThreeSum.OutputDecodeOrder.tuples_getD_indices : ∀ {α : Type u_1} (base : List.{u_1} α) (da : α)
  (hm :
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.length.{u_1} α base))
  (J k : Nat)
  (hk :
    @LT.lt.{0} Nat instLTNat k
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@List.length.{u_1} α base) J)),
  @Eq.{u_1 + 1} (List.{u_1} α)
    (@List.getD.{u_1} (List.{u_1} α) (@ThreeSum.RadixKeyLists.tuples.{u_1} α base J) k (@List.nil.{u_1} α))
    (@List.map.{0, u_1} Nat α (fun (i : Nat) => @List.getD.{u_1} α base i da)
      (ThreeSum.OutputDecodeOrder.indices (@List.length.{u_1} α base) J k)) := by
  sorry
