-- Prove2me | Theorems.Thm_ThreeSum_LightSign_meets
-- name    : ThreeSum.LightSign.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:05:02.948208+00:00
-- url     : https://prove2.me/theorems/56a40981-c56d-4149-a7c1-844bc7d9efb0
-- title:
--   Verified multiplication by a parity sign
-- statement:
--   Let $x\in\mathbb Z$, $e\in\mathbb N$, and $\mu$ be an arbitrary memory. Suppose a Light program contains the sign body, $e\le\mathrm{space}\le\mathrm{word}$, and $|x|\le\mathrm{word}$.
--
--   The call with arguments $(x,e)$ terminates within $20e+20$ steps and satisfies
--   $$
--   r=(-1)^e x,\qquad \nu=\mu.
--   $$
--   This supplies the signed scalar operation used in alternating-sum calculations, with an explicit cost linear in the exponent.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSign.lean#L19-L47

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

theorem ThreeSum.LightSign.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pMain e d : Nat} {x : Int} {μ : Nat → Int}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSign.body))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (he : @LE.le.{0} Nat instLENat e lim.space)
  (hvalue : @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup x) lim.word),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int x (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt e) (@List.nil.{0} Int))) μ
    (ThreeSum.LightSign.time e) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
            (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))) e)
          x))
      (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
