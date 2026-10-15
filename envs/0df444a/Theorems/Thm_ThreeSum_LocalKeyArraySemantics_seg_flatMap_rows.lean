-- Prove2me | Theorems.Thm_ThreeSum_LocalKeyArraySemantics_seg_flatMap_rows
-- name    : ThreeSum.LocalKeyArraySemantics.seg_flatMap_rows
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:38:10.313015+00:00
-- url     : https://prove2.me/theorems/6cadd068-93ff-4ad6-8f30-305385c0272b
-- title:
--   Uniform stored rows form the flattened list segment
-- statement:
--   Let $X$ be a list over any type, let $f$ assign an integer list to each element, and let $n,z\in\mathbb N$. Suppose every row $f(x)$ for $x\in X$ has length $n$. If integer memory $\mu$ satisfies $\mu(z+jn+i)=f(X_j)_i$ for all $j<|X|$ and $i<n$, then
--
--   $$
--   \mu[z:z+n|X|]=f(X_0)\mathbin{+\!+}\cdots\mathbin{+\!+}f(X_{|X|-1}).
--   $$
--
--   Equivalently, memory stores the list obtained by flattening the mapped rows. This connects row-wise construction invariants with contiguous list-segment specifications, including rows of length zero.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalKeyArraySemantics.lean#L18-L39

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
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
import Mathlib.Tactic.Tauto
import Theorems.Thm_Light_seg_append


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSumApsp
end ThreeSumApsp

universe u_1

theorem ThreeSum.LocalKeyArraySemantics.seg_flatMap_rows : ∀ {α : Type u_1} {μ : Nat → Int} (xs : List.{u_1} α) (f : α → List.{0} Int) (n dst : Nat)
  (hlen :
    ∀ (x : α),
      @Membership.mem.{u_1, u_1} α (List.{u_1} α) (@List.instMembership.{u_1} α) xs x →
        @Eq.{1} Nat (@List.length.{0} Int (f x)) n)
  (hread :
    ∀ (j : Nat) (hj : @LT.lt.{0} Nat instLTNat j (@List.length.{u_1} α xs)) (i : Nat)
      (hi : @LT.lt.{0} Nat instLTNat i n),
      @Eq.{1} Int
        (μ
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) j n))
            i))
        (@GetElem.getElem.{0, 0, 0} (List.{0} Int) Nat Int
          (fun (as : List.{0} Int) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Int as))
          (@List.instGetElemNatLtLength.{0} Int)
          (f
            (@GetElem.getElem.{u_1, 0, u_1} (List.{u_1} α) Nat α
              (fun (as : List.{u_1} α) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{u_1} α as))
              (@List.instGetElemNatLtLength.{u_1} α) xs j hj))
          i
          (@Eq.mpr.{0}
            (@LT.lt.{0} Nat instLTNat i
              (@List.length.{0} Int
                (f
                  (@GetElem.getElem.{u_1, 0, u_1} (List.{u_1} α) Nat α
                    (fun (as : List.{u_1} α) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{u_1} α as))
                    (@List.instGetElemNatLtLength.{u_1} α) xs j hj))))
            (@LT.lt.{0} Nat instLTNat i n)
            (@id.{0}
              (@Eq.{1} Prop
                (@LT.lt.{0} Nat instLTNat i
                  (@List.length.{0} Int
                    (f
                      (@GetElem.getElem.{u_1, 0, u_1} (List.{u_1} α) Nat α
                        (fun (as : List.{u_1} α) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{u_1} α as))
                        (@List.instGetElemNatLtLength.{u_1} α) xs j hj))))
                (@LT.lt.{0} Nat instLTNat i n))
              (@congrArg.{1, 1} Nat Prop
                (@List.length.{0} Int
                  (f
                    (@GetElem.getElem.{u_1, 0, u_1} (List.{u_1} α) Nat α
                      (fun (as : List.{u_1} α) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{u_1} α as))
                      (@List.instGetElemNatLtLength.{u_1} α) xs j hj)))
                n (fun (_a : Nat) => @LT.lt.{0} Nat instLTNat i _a)
                (hlen
                  (@GetElem.getElem.{u_1, 0, u_1} (List.{u_1} α) Nat α
                    (fun (as : List.{u_1} α) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{u_1} α as))
                    (@List.instGetElemNatLtLength.{u_1} α) xs j hj)
                  (@List.getElem_mem.{u_1} α xs j hj))))
            hi))),
  Light.Seg μ dst (@List.flatMap.{u_1, 0} α Int f xs) := by
  sorry
