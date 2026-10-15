-- Prove2me | Theorems.Thm_ThreeSum_LightSourceHistogram_Procs_meets
-- name    : ThreeSum.LightSourceHistogram.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:04:24.739465+00:00
-- url     : https://prove2.me/theorems/de74af83-2365-4b4a-9291-e9da12740fb5
-- title:
--   Execution contract for shifted source-key histograms
-- statement:
--   Let $x_i=\mu(s+i)$, $i<n$, satisfy $|x_i|\le U$. Fix positive moduli $p,m$ and an integer shift $\delta$ with $|\delta|\le E$. The program contains the source-residue and histogram procedures. Let $a,b,f$ be the histogram, code, and scratch bases, and let $S,W,D$ be its resource limits. Assume $S\le W$, $d+1<D$, $s+n,a+m\le b$, $b+n\le f$, and
--   $$f+\max\{\lfloor\log_2(U+1)\rfloor+2,\lfloor\log_2(p+E+1)\rfloor+2\}\le S,\qquad4U+8p+4E+4m+32\le W.$$
--   Writing $k_i=((x_i\bmod p)+\delta)\bmod m$, the routine produces
--   $$\nu(b+i)=k_i,\qquad\nu(a+r)=\#\{i<n:k_i=r\}\quad(r<m).$$
--   It takes at most $n(R_U+R_{p+E}+124)+13m+63$ steps, with $R_z=43(\lfloor\log_2(z+1)\rfloor+1)+34$, and preserves memory below $b$ outside the histogram.
--
--   This connects source-key arithmetic to an explicit frequency array.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceHistogram.lean#L42-L82

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
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_LightHistogram_histogram_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_ends


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightSourceHistogram.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightSourceHistogram.Procs P pMain)
  {μ : Nat → Int} {src hist n p m codes work U D : Nat} {shift : Int}
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      lim.depth)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) codes)
  (hhist : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist m) codes)
  (hcodes : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) codes n) work)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightSourceResidues.space work p U D) lim.space)
  (hshift :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup shift)
      (@Nat.cast.{0} Int instNatCastInt D))
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceResidues.word p m U D))
      lim.word)
  (hvalues :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i)))
          (@Nat.cast.{0} Int instNatCastInt U)),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt hist)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt m)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt codes)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                  (@List.cons.{0} Int shift (@List.nil.{0} Int)))))))))
    μ (ThreeSum.LightSourceHistogram.time n p m U D) fun (x : Int) (ν : Nat → Int) =>
    And
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i n →
          @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) codes i))
            (@Nat.cast.{0} Int instNatCastInt
              (ThreeSum.LightSourceResidues.key p m shift
                (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i)))))
      (And
        (∀ (r : Nat),
          @LT.lt.{0} Nat instLTNat r m →
            @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist r))
              (@Nat.cast.{0} Int instNatCastInt
                (ThreeSum.LightHistogram.count
                  (fun (i : Nat) =>
                    ThreeSum.LightSourceResidues.key p m shift
                      (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i)))
                  r n)))
        (Light.KeptBut μ ν codes hist m)) := by
  sorry
