-- Prove2me | Theorems.Thm_ThreeSum_LightSourceRetainedStages_Procs_meets
-- name    : ThreeSum.LightSourceRetainedStages.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:45:35.525041+00:00
-- url     : https://prove2.me/theorems/9145fa24-6e22-49cd-bf38-3e49aa09873c
-- title:
--   Gather a retained source function and construct all suffix stages
-- statement:
--   Let $c\le L$, $m>0$, and suppose rank-indexed endpoint and flag tables and a length-$m$ histogram are stored before destination $b$. On sets of size at most $c$, endpoints have magnitude at most $E$, flags are natural numbers at most $1$, and histogram counts are at most $B$. Define
--   $$
--   F(S)=\begin{cases}H(e(S)\bmod m),&\operatorname{flag}(S)=1,\\0,&\operatorname{flag}(S)=0.\end{cases}
--   $$
--   Reserve $(L+1)\operatorname{downsetCap}(L,c)$ destination cells, a downset-sized mask buffer, and residue/Pascal scratch satisfying the retained-source space budget. Assume its word budget, space fitting in a word, depth $d+L+8$, and the installed gather and transform procedures. The routine stores every suffix zeta stage $Z_jF$ for $j\le L$, preserves memory below $b$, and uses the gather cost plus the all-stage zeta cost and $100$ steps.
--
--   This turns retained endpoints and admissibility flags into transform-ready source tables.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceRetainedStages.lean#L60-L122

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
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
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightSourceGather_meets
import Theorems.Thm_ThreeSum_LightZetaStages_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.LightSourceRetainedStages.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (C : ThreeSum.LightSourceRetainedStages.Procs P pMain)
  {μ : Nat → Int} {raw flags table base m work L cut maskBase E B : Nat} (endpoint : Finset.{0} (Fin L) → Int)
  (flag : Finset.{0} (Fin L) → Nat) (hist : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      lim.depth)
  (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
  (hcut : @LE.le.{0} Nat instLENat cut L)
  (hraw :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw (ThreeSum.SubsetAddress.downsetCap L cut))
      base)
  (hflags :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flags (ThreeSum.SubsetAddress.downsetCap L cut))
      base)
  (htable : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) table m) base)
  (hdata :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (ThreeSum.SubsetAddress.downsetCap L cut)))
      maskBase)
  (hmasks :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maskBase
        (ThreeSum.SubsetAddress.downsetCap L cut))
      work)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightSourceRetainedStages.space work L E) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceRetainedStages.word L m E B))
      lim.word)
  (hrawRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i (ThreeSum.SubsetAddress.downsetCap L cut) →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw i))
          (endpoint (ThreeSum.SourceTableLayout.setAt L cut i)))
  (hrawBound :
    ∀ (S : Finset.{0} (Fin L)),
      @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) S) cut →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (endpoint S))
          (@Nat.cast.{0} Int instNatCastInt E))
  (hflagRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i (ThreeSum.SubsetAddress.downsetCap L cut) →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flags i))
          (@Nat.cast.{0} Int instNatCastInt (flag (ThreeSum.SourceTableLayout.setAt L cut i))))
  (hflagBound :
    ∀ (S : Finset.{0} (Fin L)),
      @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) S) cut →
        @LE.le.{0} Nat instLENat (flag S) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hhistRead :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r m →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) table r))
          (@Nat.cast.{0} Int instNatCastInt (hist r)))
  (hhistBound : ∀ (r : Nat), @LT.lt.{0} Nat instLTNat r m → @LE.le.{0} Nat instLENat (hist r) B),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt raw)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flags)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt table)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt m)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SubsetAddress.downsetCap L cut))
                        (@List.nil.{0} Int)))))))))))
    μ (ThreeSum.LightSourceRetainedStages.time L cut E) fun (x : Int) (ν : Nat → Int) =>
    And
      (@ThreeSum.LightZetaStages.StoredThrough L ν base cut
        (@ThreeSum.LightSourceRetainedStages.source L m endpoint flag hist) L)
      (Light.Kept μ ν base) := by
  sorry
