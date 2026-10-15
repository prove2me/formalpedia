-- Prove2me | Theorems.Thm_ThreeSum_LightHeaderBands_Procs_meets
-- name    : ThreeSum.LightHeaderBands.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:20:05.893078+00:00
-- url     : https://prove2.me/theorems/bebc0991-9aae-4872-82f4-dd90549183f3
-- title:
--   Read constructed band headers and execute the owner tables
-- statement:
--   Let $A,B,C$ be ordered, separated interval families with endpoint magnitudes bounded by $U$. Their memory headers store a length parameter, the family size, and the lower/upper endpoint arrays; each whole header region ends by destination $z$. Suppose the installed procedures implement the header wrapper and band enumeration. Assume the enumeration's space and word budgets fit, space fits in a word, and $d+\operatorname{width}(|A|,|B|,|C|)+5$ fits in depth. The wrapper constructs the three canonical owner-lookup rectangles and returns
--   $$
--   r=|B||C|+|A||B|+|A||C|.
--   $$
--   The resulting tables satisfy the exact band-enumeration contract at $z$, memory below $z$ is preserved, and time is the enumeration budget plus $100$.
--
--   Thus endpoint pointers and dimensions are obtained from the actual retained headers.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightHeaderBands.lean#L39-L64

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
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Mathlib.Data.List.Dedup
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
import Theorems.Thm_ThreeSum_LightBandEnumeration_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration

theorem ThreeSum.LightHeaderBands.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pMain a b c nA nB nC dst U d : Nat} {μ : Nat → Int}
  (R : ThreeSum.LightHeaderBands.Procs P pMain) (A B C : ThreeSum.BandEnumeration.Family)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (ha :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          nA)
        A.size)
      dst)
  (hb :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          nB)
        B.size)
      dst)
  (hc :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          nC)
        C.size)
      dst)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightBandEnumeration.space dst A.size B.size C.size) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBandEnumeration.word A.size B.size C.size U)) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (ThreeSum.LightBandEnumeration.width A.size B.size C.size))
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      lim.depth)
  (hA : ThreeSum.LightHeaderBands.At μ a nA A) (hB : ThreeSum.LightHeaderBands.At μ b nB B)
  (hC : ThreeSum.LightHeaderBands.At μ c nC C) (hAU : ThreeSum.LightBandEnumeration.Bounded A U)
  (hBU : ThreeSum.LightBandEnumeration.Bounded B U) (hCU : ThreeSum.LightBandEnumeration.Bounded C U),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt c)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int)))))
    μ (ThreeSum.LightHeaderBands.time A.size B.size C.size) fun (r : Int) (μ' : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBandEnumeration.count A.size B.size C.size)))
      (And (ThreeSum.LightBandEnumeration.Tables μ' dst A B C) (Light.Kept μ μ' dst)) := by
  sorry
