-- Prove2me | Theorems.Thm_ThreeSum_LightReportingWantedLayout_program_meets_relative
-- name    : ThreeSum.LightReportingWantedLayout.program_meets_relative
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:35:23.653416+00:00
-- url     : https://prove2.me/theorems/e36dbe3d-d818-42e8-8ce3-c7990f5041b1
-- title:
--   Verified reporting-scratch layout from retained scalar headers
-- statement:
--   Let $h,J,K,N,N_B,N_C,z,c,q$ be natural parameters and addresses. Put $w=512hJ$, $G=\binom{2h}h$, and $R=\operatorname{representationCap}(h,J)$. Suppose memory $\mu$ stores $G$ at $c+3$ and $R$ at $q+2$. Let $L$ be the prescribed fourteen-pointer layout rooted at $z+38+3J$, with $K+1$ frontier slots of capacity $(NN_BN_CR+1)G$ and mask span $2^w$. Define
--   $X=NN_B+NN_BN_C+NN_BN_CR+J+512h+K+N+N_B+N_C+R+G+1024$.
--   For machine limits $S,W,D$, assume $\max\{L.\mathrm{work}+X,c+4,q+3\}\le S\le W$ and $d<D$. The fixed layout program on $(J,h,K,c,q,N,N_B,N_C,z)$ finishes within $20w+2520$ steps and yields
--
--   $$
--   r=L.\mathrm{work},\qquad \nu[z:z+14]=\operatorname{values}(L).
--   $$
--
--   The list contains the root, child, count, selection, query-mask, terminal-mask, endpoint, bit, row-output, and work pointers in their prescribed order. Memory outside the header is preserved. This constructs reusable reporting scratch addresses.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedLayout.lean#L85-L249

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
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
import Mathlib.Tactic
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
import Theorems.Thm_ThreeSum_LightNatPower_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout

theorem ThreeSum.LightReportingWantedLayout.program_meets_relative : ∀ {lim : Light.Limits} {μ : Nat → Int} {dst cover counter h J K N NB NC d : Nat}
  (hgroup :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cover
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.groupSize h)))
  (hcap :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.GlobalEncoding.representationCap h J)))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hs :
    @LE.le.{0} Nat instLENat (ThreeSum.LightReportingWantedLayout.relativeSpace dst cover counter h J K N NB NC)
      lim.space),
  Light.Meets lim ThreeSum.LightReportingWantedLayout.program
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt K)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cover)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt counter)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt NB)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt NC)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int))))))))))
    μ (ThreeSum.LightReportingWantedLayout.time h J) fun (result : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int result
        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightReportingWantedLayout.layout dst h J K N NB NC).work))
      (And
        (Light.SegN ν dst
          (ThreeSum.ReportingHostWantedLayout.values (ThreeSum.LightReportingWantedLayout.layout dst h J K N NB NC)))
        (Light.SameOutside μ ν dst (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))) := by
  sorry
