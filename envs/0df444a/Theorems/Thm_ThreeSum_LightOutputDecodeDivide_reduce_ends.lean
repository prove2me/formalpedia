-- Prove2me | Theorems.Thm_ThreeSum_LightOutputDecodeDivide_reduce_ends
-- name    : ThreeSum.LightOutputDecodeDivide.reduce_ends
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:35:38.824537+00:00
-- url     : https://prove2.me/theorems/7e2bef56-f36a-42c8-8bb3-494e0b79fb21
-- title:
--   Descending modular reduction also computes the quotient
-- statement:
--   Fix resource limits with memory bound $S$ and word-magnitude bound $W$, a program, and a call depth. Let $M,V,f,a\in\mathbb N$ satisfy $M\ge1$, $a\le V$, $S\le W$, $4V+4M+16\le W$, and $f+\log_2^{\mathrm{nat}}(V+1)+2\le S$. Put $K=\operatorname{bits}(a\mathbin{/}M)$. Suppose memory $\nu$ stores the doubled-modulus table $\nu(f+j)=M2^j$ for $j<K$ and agrees with a reference memory below $f$. For any integer $t$, the quotient-reduction loop performs
--
--   $$([a,M,f,a,K,t,0],\nu)\longrightarrow([a,M,f,a\bmod M,0,t,a\mathbin{/}M],\nu)$$
--
--   within $60K+4$ steps. This supplies both quotient and remainder for the occurrence-index decoder.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightOutputDecodeDivide.lean#L43-L96

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
import Theorems.Thm_Light_Ends_while


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace Light.Emod
end Light.Emod

theorem ThreeSum.LightOutputDecodeDivide.reduce_ends : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {μ ν : Nat → Int} {a Mo V fr : Nat}
  (F : Light.Emod.Pre lim Mo V fr) (haV : @LE.le.{0} Nat instLENat a V) {t : Int}
  (tab : Light.Emod.Table μ ν Mo fr (Light.emodRounds a Mo)),
  Light.Ends lim P d ThreeSum.LightOutputDecodeDivide.reduce
    {
      loc :=
        Light.frame
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt Mo)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (Light.emodRounds a Mo))
                    (@List.cons.{0} Int t
                      (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.nil.{0} Int)))))))),
      mem := ν }
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))) (Light.emodRounds a Mo))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
    fun (σ : Light.State) =>
    @Eq.{1} Light.State σ
      {
        loc :=
          Light.frame
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt Mo)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr)
                  (@List.cons.{0} Int
                    (@Nat.cast.{0} Int instNatCastInt
                      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) a Mo))
                    (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons.{0} Int t
                        (@List.cons.{0} Int
                          (@Nat.cast.{0} Int instNatCastInt
                            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) a Mo))
                          (@List.nil.{0} Int)))))))),
        mem := ν } := by
  sorry
