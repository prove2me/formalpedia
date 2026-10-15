-- Prove2me | Theorems.Thm_ThreeSum_LightBruteThreeSum_meets
-- name    : ThreeSum.LightBruteThreeSum.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:06:40.074752+00:00
-- url     : https://prove2.me/theorems/b77e40ba-e6ad-4281-88fe-bf4dea11b069
-- title:
--   Certified exhaustive 3SUM decision on the original indices
-- statement:
--   Let $n>0$ and let $x_i\in\mathbb Z$ for $i<n$, with $|x_i|\le U$, be stored consecutively at source address $s$. Assume the program contains the specified triple scanner, row test, and division routine. Let $f\ge s+n$ be the free-memory boundary. For resource limits $S,W,D$ and entry depth $d$, require $f\le S\le W$, $n^3+3U+n+20\le W$, and $d+n^3+3\le D$.
--
--   The exhaustive routine returns a Boolean $r$ with
--   $$r=1\iff\exists i,j,k<n\text{ pairwise distinct},\quad x_i+x_j+x_k=0,$$
--   within $n^3(20(n^2+n)+650)+150$ steps, and leaves the entire memory unchanged.
--
--   This gives a verified finite fallback that checks the original positions directly, including when input values repeat.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBruteThreeSum.lean#L36-L63

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_BruteTripleIndex_hit_complete
import Theorems.Thm_ThreeSum_LightOriginalTripleScan_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec

theorem ThreeSum.LightBruteThreeSum.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pMain pScan pRow pDivide src n U fr d : Nat} (x : Fin n → Int)
  (μ : Nat → Int)
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightBruteThreeSum.body pScan)))
  (hscan :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pScan)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightOriginalTripleScan.body pScan pRow)))
  (hrow :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pRow)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightOriginalTripleRow.body pDivide)))
  (hdivide :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pDivide)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSmallDivide.body))
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) fr)
  (H : (ThreeSum.LightBruteThreeSum.need n U).Ok lim fr d)
  (hread :
    ∀ (i : Fin n),
      @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src (@Fin.val n i))) (x i))
  (hbound :
    ∀ (i : Fin n),
      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
        (@Nat.cast.{0} Int instNatCastInt U)),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt U)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr) (@List.nil.{0} Int)))))
    μ (ThreeSum.LightBruteThreeSum.time n) fun (r : Int) (ν : Nat → Int) =>
    And
      (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (And
        (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@ThreeSum.Coloring.DistinctZeroSum n x))
        (@Eq.{1} (Nat → Int) ν μ)) := by
  sorry
