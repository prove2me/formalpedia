-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverHashHistogram_meets
-- name    : ThreeSum.LightLocalCoverHashHistogram.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:04:36.513518+00:00
-- url     : https://prove2.me/theorems/52c6f03f-2eb8-4b60-9da8-777be961e8e3
-- title:
--   Constructing hash histograms while preserving neighboring tables
-- statement:
--   Memory stores $n$ masks $q_i<2^L$ and natural coefficient rows $w_0,w_1\le U$. For $p>0$, define
--   $$c_i=\left(\sum_{a<L}(\operatorname{bit}_a(q_i)?w_1(a):w_0(a))\right)\bmod p.$$
--   All input arrays end before raw-output base $r$; require $r+n\le c$, $c+n\le h$, and $h+p\le w$. Assume the specified hash, residue, and histogram procedures,
--   $$w+\max(L+1,\lfloor\log_2(LU+1)\rfloor+2)\le S\le B,\quad d+L+2\le D,$$
--   $$2^{L+1}+(L+1)U+4LU+4p+16\le B.$$
--   The routine writes $\nu(c+i)=c_i$ and $\nu(h+s)=\#\{i<n:c_i=s\}$ for $s<p$. With $\lambda=\lfloor\log_2(LU+1)\rfloor$, its budget is
--   $$n(100L+43\lambda+231)+17L+13p+198.$$
--   Below $w$, every cell outside the raw, code, and histogram intervals is preserved; in particular, all cells below $r$ are preserved.
--
--   This permits neighboring completed candidate tables to survive the next hash construction.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverHashHistogram.lean#L21-L96

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
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
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
import Theorems.Thm_ThreeSum_LightHistogram_histogram_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_meets
import Theorems.Thm_ThreeSum_LightResidues_residues_ends
import Theorems.Thm_ThreeSum_OneHotMask_eval_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHashHistogram
end ThreeSum.LightHashHistogram

theorem ThreeSum.LightLocalCoverHashHistogram.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightHashHistogram.Procs P pMain)
  {μ : Nat → Int} {L masks raw codes hist n src0 src1 p work U : Nat} (mask w0 w1 : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      lim.depth)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightHashHistogram.space work L U) lim.space)
  (hmasks : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks n) raw)
  (hsrc0 : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src0 L) raw)
  (hsrc1 : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src1 L) raw)
  (hraw : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw n) codes)
  (hcodes : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) codes n) hist)
  (hhist : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist p) work)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightHashHistogram.word L p U)) lim.word)
  (hmaskRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks i))
          (@Nat.cast.{0} Int instNatCastInt (mask i)))
  (hmaskLt :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LT.lt.{0} Nat instLTNat (mask i)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L))
  (hread0 :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i L →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src0 i))
          (@Nat.cast.{0} Int instNatCastInt (w0 i)))
  (hread1 :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i L →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src1 i))
          (@Nat.cast.{0} Int instNatCastInt (w1 i)))
  (hbound0 : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w0 i) U)
  (hbound1 : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w1 i) U),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt raw)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt codes)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt hist)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src0)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src1)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work) (@List.nil.{0} Int)))))))))))
    μ (ThreeSum.LightHashHistogram.time L n p U) fun (x : Int) (μ' : Nat → Int) =>
    And
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i n →
          @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) codes i))
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightHashHistogram.code L p mask w0 w1 i)))
      (And
        (∀ (r : Nat),
          @LT.lt.{0} Nat instLTNat r p →
            @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist r))
              (@Nat.cast.{0} Int instNatCastInt
                (ThreeSum.LightHistogram.count (ThreeSum.LightHashHistogram.code L p mask w0 w1) r n)))
        (And (Light.Kept μ μ' raw) (ThreeSum.LightLocalCoverHashHistogram.Preserved μ μ' work raw codes hist n p))) := by
  sorry
