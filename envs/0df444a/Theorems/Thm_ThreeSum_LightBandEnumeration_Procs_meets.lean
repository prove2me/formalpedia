-- Prove2me | Theorems.Thm_ThreeSum_LightBandEnumeration_Procs_meets
-- name    : ThreeSum.LightBandEnumeration.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:08:42.597699+00:00
-- url     : https://prove2.me/theorems/0ae83664-b75a-41c5-ac56-03d607513978
-- title:
--   Execution contract for the three band-enumeration lookup tables
-- statement:
--   Let $A,B,C$ be ordered families of separated nonempty intervals, with sizes $a,b,c$ and endpoint magnitudes at most $U$. Their six endpoint arrays are stored entirely below destination $z$. Set $N=a+b+c$, $w=\lceil\log_2(N+1)\rceil$, and $R=bc+ab+ac$. Assume the specified logarithm, power-table, and lookup procedures, with
--   $$z+R+w+1\le S\le W,\qquad8(N+U+1)+32\le W,\qquad d+w+4\le D.$$
--   The routine returns $R$ and writes the consecutive $BC$, $AB$, and $AC$ lookup tables for the queries $C_{\rm lo}-B_{\rm hi}$ into $A$, $A_{\rm lo}+B_{\rm lo}$ into $C$, and $C_{\rm lo}-A_{\rm lo}$ into $B$. Each entry is zero on failure and otherwise one plus the matching index. Memory below $z$ is preserved.
--
--   The step bound is the logarithm-table setup, power-table setup, and the three rectangular table bounds $T(b,c,w)+T(a,b,w)+T(a,c,w)+500$, where $T(u,v,w)=u(v(120w+190)+76)+6$.
--
--   This certifies the physical lookup arrays used to enumerate candidate band triples.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandEnumeration.lean#L95-L257

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Theorems.Thm_Light_clog2_meets
import Theorems.Thm_Light_powTable_ends
import Theorems.Thm_ThreeSum_KaratsubaInterface_capacity_lt_twice
import Theorems.Thm_ThreeSum_LightBandTable_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace Light.PowTable
end Light.PowTable
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.LightBandEnumeration.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pMain al ah bl bh cl ch dst U d : Nat} {μ : Nat → Int}
  (R : ThreeSum.LightBandEnumeration.Procs P pMain) (A B C : ThreeSum.BandEnumeration.Family)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hal : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) al A.size) dst)
  (hah : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ah A.size) dst)
  (hbl : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bl B.size) dst)
  (hbh : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bh B.size) dst)
  (hcl : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cl C.size) dst)
  (hch : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ch C.size) dst)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightBandEnumeration.space dst A.size B.size C.size) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBandEnumeration.word A.size B.size C.size U)) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (ThreeSum.LightBandEnumeration.width A.size B.size C.size))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      lim.depth)
  (hA : ThreeSum.LightBandEnumeration.At μ al ah A) (hB : ThreeSum.LightBandEnumeration.At μ bl bh B)
  (hC : ThreeSum.LightBandEnumeration.At μ cl ch C) (hAU : ThreeSum.LightBandEnumeration.Bounded A U)
  (hBU : ThreeSum.LightBandEnumeration.Bounded B U) (hCU : ThreeSum.LightBandEnumeration.Bounded C U),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt al)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ah)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bl)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bh)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cl)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ch)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt A.size)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt B.size)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt C.size)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int)))))))))))
    μ (ThreeSum.LightBandEnumeration.time A.size B.size C.size) fun (r : Int) (μ' : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBandEnumeration.count A.size B.size C.size)))
      (And (ThreeSum.LightBandEnumeration.Tables μ' dst A B C) (Light.Kept μ μ' dst)) := by
  sorry
