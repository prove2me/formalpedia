-- Prove2me | Theorems.Thm_ThreeSum_LightWantedRow_meets
-- name    : ThreeSum.LightWantedRow.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:05:36.79343+00:00
-- url     : https://prove2.me/theorems/c7d81115-185c-43e8-a550-faaa3cd3ce27
-- title:
--   Verified emission of one row of wanted index pairs
-- statement:
--   Let $\ell,s,u,n,z,p$ be natural numbers: the left label, source base, source offset, row length, destination base, and number of previously emitted pairs. Let $\mu$ be integer memory and $S,W$ the machine space and word bounds. Assume $s+u+n\le z$, $z+2(p+n)\le S\le W$, $\ell\le W$, and $|\mu(s+u+t)|\le W$ for every $t<n$. If the called procedure is the wanted-row body, execution on $(\ell,s,u,n,z,p)$ at any depth finishes within $120n+20$ steps and yields
--
--   $$
--   \nu(z+2(p+t))=\ell,\qquad
--   \nu(z+2(p+t)+1)=\mu(s+u+t)\quad(t<n).
--   $$
--
--   Memory outside $[z+2p,z+2(p+n))$ is preserved. This appends a fixed left label paired with every entry of a selected source bucket.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWantedRow.lean#L33-L82

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
import Theorems.Thm_Light_Ends_for


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightWantedRow.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain left src start n dst previous : Nat} {μ : Nat → Int}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt ThreeSum.LightWantedRow.body))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hsrc :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src start) n)
      dst)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) previous n)))
      lim.space)
  (hleft : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt left) lim.word)
  (hvalues :
    ∀ (t : Nat),
      @LT.lt.{0} Nat instLTNat t n →
        @LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (μ
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src start) t)))
          lim.word),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt left)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt start)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt previous) (@List.nil.{0} Int)))))))
    μ (ThreeSum.LightWantedRow.time n) fun (x : Int) (ν : Nat → Int) =>
    And
      (∀ (t : Nat),
        @LT.lt.{0} Nat instLTNat t n →
          And
            (@Eq.{1} Int
              (ν
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) previous t))))
              (@Nat.cast.{0} Int instNatCastInt left))
            (@Eq.{1} Int
              (ν
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) previous t)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src start) t))))
      (Light.SameOutside μ ν
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) previous))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)) := by
  sorry
