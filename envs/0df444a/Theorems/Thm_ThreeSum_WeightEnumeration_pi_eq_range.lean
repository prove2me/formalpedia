-- Prove2me | Theorems.Thm_ThreeSum_WeightEnumeration_pi_eq_range
-- name    : ThreeSum.WeightEnumeration.pi_eq_range
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:44:17.650602+00:00
-- url     : https://prove2.me/theorems/53803279-c960-449c-aa20-7a67687706d1
-- title:
--   Ordered Cartesian enumeration equals radix decoding
-- statement:
--   Let $\iota$ be an index type with decidable equality, and let $K$ carry a specified natural-number cast $c:\mathbb N\to K$. Let $p\in\mathbb N$ and let $l$ be a finite list of indices. Form the ordered Cartesian-product list $\Pi_l$ by choosing each coordinate from $[c(0),\ldots,c(p-1)]$, with the first list position varying most slowly. Let $D_{p,l}(k)$ be the recursive decoder that reads the most significant digit first; repeated labels use their first occurrence. Then
--
--   $$\Pi_l=\bigl[D_{p,l}(0),D_{p,l}(1),\ldots,D_{p,l}(p^{|l|}-1)\bigr].$$
--
--   This is equality of lists, including their order and repetitions. It identifies the original coefficient enumeration with concrete radix indices without assuming distinct labels or an injective cast.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/WeightEnumeration.lean#L35-L55

import Aesop
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

universe u_1 u_2

theorem ThreeSum.WeightEnumeration.pi_eq_range : ∀ {ι : Type u_1} {K : Type u_2} [inst : DecidableEq.{u_1 + 1} ι] [inst_1 : NatCast.{u_2} K] (p : Nat)
  (l : List.{u_1} ι),
  @Eq.{max (u_1 + 1) (u_2 + 1)}
    (List.{max u_1 u_2} ((i : ι) → @Membership.mem.{u_1, u_1} ι (List.{u_1} ι) (@List.instMembership.{u_1} ι) l i → K))
    (@List.pi.{u_1, u_2} ι inst (fun (x : ι) => K) l fun (x : ι) =>
      @List.map.{0, u_2} Nat K (fun (n : Nat) => @Nat.cast.{u_2} K inst_1 n) (List.range p))
    (@List.map.{0, max u_1 u_2} Nat
      ((i : ι) → @Membership.mem.{u_1, u_1} ι (List.{u_1} ι) (@List.instMembership.{u_1} ι) l i → K)
      (@ThreeSum.WeightEnumeration.decode.{u_1, u_2} ι K inst inst_1 p l)
      (List.range
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
          (@List.length.{u_1} ι l)))) := by
  sorry
