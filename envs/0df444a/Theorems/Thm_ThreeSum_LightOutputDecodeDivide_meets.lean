-- Prove2me | Theorems.Thm_ThreeSum_LightOutputDecodeDivide_meets
-- name    : ThreeSum.LightOutputDecodeDivide.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:05:20.726049+00:00
-- url     : https://prove2.me/theorems/c8caa2a7-91e5-4260-b426-0e2f682d8053
-- title:
--   Verified logarithmic division for decoding output indices
-- statement:
--   Let $a,M,V,f$ be natural numbers with $M\ge1$ and $a\le V$, and let $\mu$ be integer memory. For machine space and word bounds $S,W$, assume $S\le W$, $4V+4M+16\le W$, and $f+\lfloor\log_2(V+1)\rfloor+2\le S$. If the called procedure in $P$ is the output-decoding divider, execution on $(a,M,f)$ at any depth finishes within $80K+100$ steps, where $K$ is the binary bit length of $\lfloor a/M\rfloor$ and the bit length of zero is zero. Its result and final memory satisfy
--
--   $$
--   q=\left\lfloor\frac aM\right\rfloor,\qquad
--   \nu(x)=\mu(x)\quad(x<f).
--   $$
--
--   The free region beginning at $f$ provides scratch space for division while preserving previously constructed data.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightOutputDecodeDivide.lean#L98-L116

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
import Theorems.Thm_Light_Emod_table_ends
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_reduce_ends


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace Light.Emod
end Light.Emod

theorem ThreeSum.LightOutputDecodeDivide.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {μ : Nat → Int} {a Mo V fr pMain : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt ThreeSum.LightOutputDecodeDivide.body))
  (F : Light.Emod.Pre lim Mo V fr) (haV : @LE.le.{0} Nat instLENat a V),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt Mo)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr) (@List.nil.{0} Int))))
    μ (ThreeSum.LightOutputDecodeDivide.time a Mo) fun (q : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int q
        (@Nat.cast.{0} Int instNatCastInt (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) a Mo)))
      (Light.Kept μ ν fr) := by
  sorry
