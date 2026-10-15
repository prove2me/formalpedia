-- Prove2me | Theorems.Thm_ThreeSum_LightSourceResidues_ends
-- name    : ThreeSum.LightSourceResidues.ends
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:37:45.501389+00:00
-- url     : https://prove2.me/theorems/66e33d98-3022-47da-8a4c-9cdb282b20c7
-- title:
--   Verified two-modulus source residue scan with a signed shift
-- statement:
--   Let $p,m>0$, let $\delta\in\mathbb Z$ satisfy $|\delta|\le D_0$, and let integer memory $\mu$ have $|\mu(s+i)|\le U$ for $i<n$. Source and destination segments $[s,s+n)$ and $[z,z+n)$ are disjoint and end at or before work base $f$. Define $R_v=43(\lfloor\log_2(v+1)\rfloor+1)+34$. For machine limits $S,W,D$, assume $S\le W$, $d<D$,
--   $f+\max\{\lfloor\log_2(U+1)\rfloor+2,\lfloor\log_2(p+D_0+1)\rfloor+2\}\le S$, and $4U+8p+4D_0+4m+32\le W$. With the specified Euclidean-remainder helper, the source-residue body on $(s,z,n,p,m,f,\delta)$ finishes within $n(R_U+R_{p+D_0}+100)+6$ steps and gives
--
--   $$
--   \mu'(z+i)=\bigl(\mu(s+i)\bmod p+\delta\bigr)\bmod m\quad(i<n).
--   $$
--
--   Memory below $f$ outside the destination is preserved. This constructs the exact shifted source codes used by histogram and join stages.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceResidues.lean#L55-L132

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
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_Light_emod_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightSourceResidues.ends : ∀ {lim : Light.Limits} {P : Light.Program} {d pEmod : Nat}
  (hem :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEmod)
      (@Option.some.{0} Light.Stmt Light.emodBody))
  {μ : Nat → Int} {src dst n p m work U D : Nat} {shift : Int}
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) work)
  (hdst : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst n) work)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightSourceResidues.space work p U D) lim.space)
  (hsep : Light.Apart src n dst n)
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
  Light.Ends lim P d (ThreeSum.LightSourceResidues.body pEmod)
    {
      loc :=
        Light.frame
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt m)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                      (@List.cons.{0} Int shift (@List.nil.{0} Int)))))))),
      mem := μ }
    (ThreeSum.LightSourceResidues.time n p U D) fun (σ : Light.State) =>
    And
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i n →
          @Eq.{1} Int (σ.mem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst i))
            (@Nat.cast.{0} Int instNatCastInt
              (ThreeSum.LightSourceResidues.key p m shift
                (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i)))))
      (Light.KeptBut μ σ.mem work dst n) := by
  sorry
