-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawAColor_Procs_meets
-- name    : ThreeSum.LightBandRawAColor.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:41:20.833512+00:00
-- url     : https://prove2.me/theorems/b2885e87-2f0a-4407-a3c7-d9a3c0d423af
-- title:
--   Construct colored band records and their physical source incidences
-- statement:
--   Let $p$ be a width-$w$ coloring of an integer input $x$ of length $n$, with $n\le2^w$, $|x_i|\le U$, and band size $g>0$. Reserve the ordered color-class and normalized-band areas, followed by lookup-table base $z$, record base $r_0\ge z+R$, and physical-value base $v\ge r_0+4R$, where $R=3\lceil n/g\rceil^2$. Assume the specified procedures and the exact composite space, word, and depth budgets, with $S\le W$.
--
--   Execution produces normalized lists $A,B,C$ with the three color classes' exact memberships, their headers and lookup tables, and the sorted candidate records $\mathcal R$. It then stores the associated physical source values, owners, and original positions, returning
--   $$r=|\operatorname{items}(|A|,g,\mathcal R)|.$$
--   The time is the color-band budget plus $3000(R+3\lceil n/g\rceil+1)(g+1)+300$, and memory before the color area is preserved.
--
--   This connects the colored input to the concrete incidence arrays consumed by later source and reporting stages.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandRawAColor.lean#L91-L182

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
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
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
import Theorems.Thm_ThreeSum_LightBandPreprocessing_Represents_keep
import Theorems.Thm_ThreeSum_LightBandRawACatalog_Procs_meets
import Theorems.Thm_ThreeSum_LightBandRawAColor_tables_keep
import Theorems.Thm_ThreeSum_LightColorBands_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

theorem ThreeSum.LightBandRawAColor.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program}
  {d pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work rec vals U : Nat} {μ : Nat → Int}
  (R : ThreeSum.LightBandRawAColor.Procs P pMain) (p : ThreeSum.Coloring.Parameter W) (x : Fin n → Int)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hn :
    @LE.le.{0} Nat instLENat n
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W))
  (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) colors)
  (hcolors : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) colors n) dst0)
  (h0 :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst0 n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      dst1)
  (h1 :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst1 n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      dst2)
  (h2 :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst2 n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      av)
  (hav : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) av n) ae)
  (hae :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ae
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      bv)
  (hbv : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bv n) be)
  (hbe :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) be
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      cv)
  (hcv : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cv n) ce)
  (hce :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ce
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      work)
  (htable :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work (ThreeSum.ColorBandBounds.count n g)) rec)
  (hrec :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rec
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (ThreeSum.ColorBandBounds.count n g)))
      vals)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightBandRawAColor.space work vals W n g) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBandRawAColor.word W n g U)) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d (ThreeSum.LightBandRawAColor.depth W n g))
      lim.depth)
  (hread : Light.Seg μ src (@List.ofFn.{0} Int n x))
  (hbound :
    ∀ (i : Fin n),
      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
        (@Nat.cast.{0} Int instNatCastInt U)),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
          (@List.cons.{0} Int
            (@Nat.cast.{0} Int instNatCastInt
              (@Fin.val W
                (@Prod.fst.{0, 0} (Fin W) (Fin W)
                  (@Prod.fst.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                    (Prod.{0, 0} Bool Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) p))))
            (@List.cons.{0} Int
              (@Nat.cast.{0} Int instNatCastInt
                (@Fin.val W
                  (@Prod.snd.{0, 0} (Fin W) (Fin W)
                    (@Prod.fst.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                      (Prod.{0, 0} Bool Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) p))))
              (@List.cons.{0} Int
                (@Nat.cast.{0} Int instNatCastInt
                  (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                      (Prod.{0, 0} Bool Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) p
                      (@Prod.mk.{0, 0} Bool Bool Bool.false Bool.false))))
                (@List.cons.{0} Int
                  (@Nat.cast.{0} Int instNatCastInt
                    (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                        (Prod.{0, 0} Bool Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) p
                        (@Prod.mk.{0, 0} Bool Bool Bool.false Bool.true))))
                  (@List.cons.{0} Int
                    (@Nat.cast.{0} Int instNatCastInt
                      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                          (Prod.{0, 0} Bool Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) p
                          (@Prod.mk.{0, 0} Bool Bool Bool.true Bool.false))))
                    (@List.cons.{0} Int
                      (@Nat.cast.{0} Int instNatCastInt
                        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                            (Prod.{0, 0} Bool Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            p (@Prod.mk.{0, 0} Bool Bool Bool.true Bool.true))))
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt colors)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst0)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst1)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst2)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt g)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt av)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ae)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bv)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt be)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cv)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ce)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rec)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt vals)
                                                  (@List.nil.{0} Int))))))))))))))))))))))))
    μ (ThreeSum.LightBandRawAColor.time W n g) fun (r : Int) (ν : Nat → Int) =>
    And
      (ThreeSum.LightBandRawAColor.Output ν av ae bv be cv ce work rec vals g hg
        (@ThreeSum.ColorClassLists.classList n W p x (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@ThreeSum.ColorClassLists.classList n W p x (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@ThreeSum.ColorClassLists.classList n W p x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        r)
      (Light.Kept μ ν colors) := by
  sorry
