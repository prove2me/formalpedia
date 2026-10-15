-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverSetup_Procs_meets
-- name    : ThreeSum.LightLocalCoverSetup.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:44:51.944484+00:00
-- url     : https://prove2.me/theorems/f8dd8b76-b75d-4cf8-83e4-367a7bebf7aa
-- title:
--   Compute the complete local-cover layout and selected schedule
-- statement:
--   For $h\in\mathbb N$, put $L=512h$, $p=\operatorname{localPrime}(h)$, $v=\binom Lh$, and $c=\operatorname{localBucketCap}(h)$. Starting at address $b$, assume the power, logarithm, and cover-building procedures are installed, the local-cover layout and word budgets fit, space fits in a word, and depth $d+L+8$ is available. The setup procedure constructs all candidate coefficient maps, their two residue histograms and cover matrix, and the exact greedy schedule. In particular,
--   $$
--   \mu'(\operatorname{candidates}(b,h)+s)=\operatorname{candidateAt}(h,s)
--   \quad(s<\operatorname{scheduleSize}(h)).
--   $$
--   It returns the address of the selected schedule maps and preserves memory below $b$. The time budget is $\operatorname{powerTime}(2L)+\operatorname{logTime}(p^2)+\operatorname{coverBuildTime}(h)+500$.
--
--   The construction derives candidate counts and table addresses from the scalar graph parameters.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverSetup.lean#L55-L209

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.Data.List.Range
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
import Theorems.Thm_Light_log2_meets
import Theorems.Thm_ThreeSum_LightLocalCoverBuild_Procs_meets
import Theorems.Thm_ThreeSum_LightNatPower_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds

theorem ThreeSum.LightLocalCoverSetup.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightLocalCoverSetup.Procs P pMain)
  {μ : Nat → Int} {base h : Nat}
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      lim.depth)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightLocalCoverLayout.space base h) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverSetup.word h)) lim.word),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localPrime h))
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverLayout.vertices h))
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localBucketCap h))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base) (@List.nil.{0} Int))))))
    μ (ThreeSum.LightLocalCoverSetup.time h) fun (r : Int) (ν : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverLayout.scheduleMaps base h)))
      (And
        (ThreeSum.LightLocalCoverTables.Data ν h (ThreeSum.LightLocalCoverLayout.maps base h)
          (ThreeSum.LightLocalCoverLayout.hist0 base h) (ThreeSum.LightLocalCoverLayout.hist1 base h)
          (ThreeSum.LightLocalCoverLayout.matrixPtr base h))
        (And (ThreeSum.LightLocalCoverTables.ScheduleRows ν h (ThreeSum.LightLocalCoverLayout.scheduleMaps base h))
          (And
            (∀ (s : ThreeSum.GlobalEncoding.Occurrence h),
              @Eq.{1} Int
                (ν
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ThreeSum.LightLocalCoverLayout.candidates base h)
                    (@Fin.val (ThreeSum.GlobalEncoding.scheduleSize h) s)))
                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverSchedule.candidateAt h s)))
            (Light.Kept μ ν base)))) := by
  sorry
