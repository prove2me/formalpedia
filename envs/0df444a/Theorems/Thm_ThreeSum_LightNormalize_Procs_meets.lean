-- Prove2me | Theorems.Thm_ThreeSum_LightNormalize_Procs_meets
-- name    : ThreeSum.LightNormalize.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:12:26.827744+00:00
-- url     : https://prove2.me/theorems/60c61e20-3a99-437b-8dad-239bfaf595ec
-- title:
--   Normalization returns the strictly increasing list of distinct values
-- statement:
--   Let an integer list $L$ of length $n$ occupy memory at source address $s$. Assume the program contains the specified sorting and deduplication procedures. Reserve an output buffer at $a$ and scratch at $f$ with $s+n\le a$, $a+n\le f$, and $f+n\le S\le W$. Require $1\le W$ and entry depth $d+n+\lceil\log_2 n\rceil+2\le D$.
--
--   The routine returns the length of a list $L'$ stored at $a$, where
--   $$L'\text{ is strictly increasing},\qquad |L'|\le n,\qquad z\in L'\iff z\in L.$$
--   Its step bound is $61n\lceil\log_2n\rceil+74(n-1)+200n+114$, with natural subtraction and the formal logarithm convention at zero. Memory below $f$ outside both reserved source and output intervals is preserved.
--
--   This provides sorted, duplicate-free values while retaining the exact membership information needed by later band constructions.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightNormalize.lean#L143-L170

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
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Theorems.Thm_Light_sort_meets
import Theorems.Thm_ThreeSum_LightNormalize_dedup_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightNormalize.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pMain src dst work d : Nat} {L : List.{0} Int} {μ : Nat → Int}
  (C : ThreeSum.LightNormalize.Procs P pMain)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (h1 : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) lim.word)
  (hseg : Light.Seg μ src L)
  (hsep :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src (@List.length.{0} Int L)) dst)
  (hwork :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst (@List.length.{0} Int L)) work)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightNormalize.space work (@List.length.{0} Int L)) lim.space)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d (@List.length.{0} Int L))
          (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int L)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      lim.depth),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int L))
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work) (@List.nil.{0} Int)))))
    μ (ThreeSum.LightNormalize.time (@List.length.{0} Int L)) fun (r : Int) (μ' : Nat → Int) =>
    ∃ (out : List.{0} Int),
      And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int out)))
        (And (Light.Seg μ' dst out)
          (And (@List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) out)
            (And (@LE.le.{0} Nat instLENat (@List.length.{0} Int out) (@List.length.{0} Int L))
              (And
                (∀ (z : Int),
                  Iff (@Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) out z)
                    (@Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) L z))
                (∀ (a : Nat),
                  @LT.lt.{0} Nat instLTNat a work →
                    Or (@LT.lt.{0} Nat instLTNat a src)
                        (@LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src (@List.length.{0} Int L))
                          a) →
                      Or (@LT.lt.{0} Nat instLTNat a dst)
                          (@LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                              (@List.length.{0} Int L))
                            a) →
                        @Eq.{1} Int (μ' a) (μ a)))))) := by
  sorry
