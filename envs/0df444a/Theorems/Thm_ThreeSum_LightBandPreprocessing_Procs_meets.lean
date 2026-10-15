-- Prove2me | Theorems.Thm_ThreeSum_LightBandPreprocessing_Procs_meets
-- name    : ThreeSum.LightBandPreprocessing.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:33:04.505646+00:00
-- url     : https://prove2.me/theorems/a518b92b-df6f-4aaa-8ee5-9e081d3f7c1c
-- title:
--   Sorting, deduplicating, and enumerating the three band families
-- statement:
--   Let three stored integer lists have lengths $a,b,c$ and absolute values bounded by $U$, and fix $g>0$. The sources occur in order before three output pairs: a value region of capacity equal to its original length, followed by a header/endpoint region of capacity twice that length plus two. All output pairs precede the common scratch/table base $w$.
--
--   Assume the specified sorted-band preparation and header-enumeration procedures. With machine limits $S,W,D$, require $S\le W$ and the routine's defined space, word, and depth budgets at $(a,b,c,g,U)$ to fit. The procedure produces strictly increasing lists $A,B,C$ satisfying
--   $$|A|\le a,\quad\{x:x\in A\}=\{x:x\in A_{\mathrm{original}}\},$$
--   and the analogous properties for $B,C$. It stores their exact consecutive-band headers and endpoints and all three owner-lookup tables at $w$. The return value is the total table-cell count $n_Bn_C+n_An_B+n_An_C$, for the resulting band counts. Cells below the first source base are preserved, and the declared preprocessing time bound holds.
--
--   This constructs the normalized band representation used by owner enumeration.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandPreprocessing.lean#L89-L221

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_LightBandPreprocessing_Represents_keep
import Theorems.Thm_ThreeSum_LightHeaderBands_Procs_meets
import Theorems.Thm_ThreeSum_LightSortedBands_Prepared_transfer
import Theorems.Thm_ThreeSum_LightSortedBands_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

theorem ThreeSum.LightBandPreprocessing.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pMain srcA srcB srcC av ae bv be cv ce work g U d : Nat} {μ : Nat → Int}
  {originalA originalB originalC : List.{0} Int} (R : ThreeSum.LightBandPreprocessing.Procs P pMain)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g)
  (hsrcAB :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcA (@List.length.{0} Int originalA)) srcB)
  (hsrcBC :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB (@List.length.{0} Int originalB)) srcC)
  (hsrcCv :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcC (@List.length.{0} Int originalC)) av)
  (hav :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) av (@List.length.{0} Int originalA)) ae)
  (hae :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ae
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int originalA)))
      bv)
  (hbv :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bv (@List.length.{0} Int originalB)) be)
  (hbe :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) be
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int originalB)))
      cv)
  (hcv :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cv (@List.length.{0} Int originalC)) ce)
  (hce :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ce
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int originalC)))
      work)
  (hspace :
    @LE.le.{0} Nat instLENat
      (ThreeSum.LightBandPreprocessing.space work (@List.length.{0} Int originalA) (@List.length.{0} Int originalB)
        (@List.length.{0} Int originalC) g)
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.LightBandPreprocessing.word (@List.length.{0} Int originalA) (@List.length.{0} Int originalB)
          (@List.length.{0} Int originalC) g U))
      lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (ThreeSum.LightBandPreprocessing.depth (@List.length.{0} Int originalA) (@List.length.{0} Int originalB)
          (@List.length.{0} Int originalC) g))
      lim.depth)
  (hAread : Light.Seg μ srcA originalA) (hBread : Light.Seg μ srcB originalB) (hCread : Light.Seg μ srcC originalC)
  (hAU :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) originalA z →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z)
          (@Nat.cast.{0} Int instNatCastInt U))
  (hBU :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) originalB z →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z)
          (@Nat.cast.{0} Int instNatCastInt U))
  (hCU :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) originalC z →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z)
          (@Nat.cast.{0} Int instNatCastInt U)),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcA)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int originalA))
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcB)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int originalB))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcC)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int originalC))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt g)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt av)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ae)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bv)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt be)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cv)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ce)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                (@List.nil.{0} Int)))))))))))))))
    μ
    (ThreeSum.LightBandPreprocessing.time (@List.length.{0} Int originalA) (@List.length.{0} Int originalB)
      (@List.length.{0} Int originalC) g)
    fun (r : Int) (μ' : Nat → Int) =>
    And (ThreeSum.LightBandPreprocessing.Output μ' av ae bv be cv ce work g hg originalA originalB originalC r)
      (Light.Kept μ μ' srcA) := by
  sorry
