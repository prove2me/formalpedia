-- Prove2me | Theorems.Thm_ThreeSum_ThreeSumWantedHostConditions_actual_separation
-- name    : ThreeSum.ThreeSumWantedHostConditions.actual_separation
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:07:08.789799+00:00
-- url     : https://prove2.me/theorems/8722918a-ce04-4b7b-b97b-1a1322e1dd61
-- title:
--   Actual auxiliary moduli separate every nonzero band difference
-- statement:
--   Let $x_i$ ($i<n$) be integers with $|x_i|\le n^k$, and let $A,B,C$ be the strictly increasing lists stored by the encoded color pipeline for a fixed coloring. Use the actual band size and its sorted records to enumerate the finite band products. Assume the readiness predicate for $k,n$: positive input and micro-block size, radix at least four, the prescribed divisor-budget inequality, and an auxiliary modulus not dividing every nonzero integer of absolute value at most $3n^k$.
--
--   For a band-product entry $t$, write $\Delta(t)=C_{t_C}-B_{t_B}-A_{\rm phys}(t_A)$, where $A_{\rm phys}$ is the source value selected by the stored record. Then
--   $$\Delta(t)\ne0\ \Longrightarrow\ \exists\ell\in\mathcal A_n,\quad\ell\nmid\Delta(t),$$
--   where $\mathcal A_n$ is the auxiliary-modulus set generated from the actual prime pool.
--
--   This transfers the numerical separation premise to the concrete products consumed by the host.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumWantedHostConditions.lean#L65-L101

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
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
import Definitions.Def_ThreeSum1962Source_Bundle16
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BandRawA_product_values_mem


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
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales

theorem ThreeSum.ThreeSumWantedHostConditions.actual_separation : ∀ {μ : Nat → Int} {free n k : Nat}
  {color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {x : Fin n → Int} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  (H : ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
  (hn : ThreeSum.ThreeSumWantedHostConditions.Ready k n)
  (hx :
    ∀ (i : Fin n),
      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
        (@Nat.cast.{0} Int instNatCastInt
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) n k))),
  have rs :=
    ThreeSum.BandRawA.sortedRecords A B C (ThreeSum.BandScales.bandSize n) (ThreeSum.BandScales.bandSize_pos n) hsA hsB
      hsC;
  ∀
    (t :
      Prod.{0, 0}
        (Fin
          (@List.length.{0} ThreeSum.BandRawA.Label
            (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
        (Prod.{0, 0} (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C)))),
    @Membership.mem.{0, 0}
        (Prod.{0, 0}
          (Fin
            (@List.length.{0} ThreeSum.BandRawA.Label
              (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
          (Prod.{0, 0} (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C))))
        (Finset.{0}
          (Prod.{0, 0}
            (Fin
              (@List.length.{0} ThreeSum.BandRawA.Label
                (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
            (Prod.{0, 0} (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C)))))
        (@SetLike.instMembership.{0, 0}
          (Finset.{0}
            (Prod.{0, 0}
              (Fin
                (@List.length.{0} ThreeSum.BandRawA.Label
                  (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
              (Prod.{0, 0} (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C)))))
          (Prod.{0, 0}
            (Fin
              (@List.length.{0} ThreeSum.BandRawA.Label
                (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
            (Prod.{0, 0} (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C))))
          (@Finset.instSetLike.{0}
            (Prod.{0, 0}
              (Fin
                (@List.length.{0} ThreeSum.BandRawA.Label
                  (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
              (Prod.{0, 0} (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C))))))
        (ThreeSum.BandRawA.finiteAllProducts (@List.length.{0} Int A) (@List.length.{0} Int B) (@List.length.{0} Int C)
          (ThreeSum.BandScales.bandSize n) rs)
        t →
      @Ne.{1} Int
          (@ThreeSum.RawIncidences.difference.{0, 0, 0}
            (Fin
              (@List.length.{0} ThreeSum.BandRawA.Label
                (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
            (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C))
            (fun
                (i :
                  Fin
                    (@List.length.{0} ThreeSum.BandRawA.Label
                      (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs))) =>
              ThreeSum.BandRawA.valueAt (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs
                (fun (j : Nat) => @List.getD.{0} Int A j (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                (@Fin.val
                  (@List.length.{0} ThreeSum.BandRawA.Label
                    (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs))
                  i))
            (fun (i : Fin (@List.length.{0} Int B)) =>
              @List.getD.{0} Int B (@Fin.val (@List.length.{0} Int B) i)
                (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (fun (i : Fin (@List.length.{0} Int C)) =>
              @List.getD.{0} Int C (@Fin.val (@List.length.{0} Int C) i)
                (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            t)
          (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
        ∃ (l : Int),
          And
            (@Membership.mem.{0, 0} Int (Finset.{0} Int)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
              (ThreeSum.DenseGuard.actualAux n) l)
            (Not
              (@Dvd.dvd.{0} Int Int.instDvd l
                (@ThreeSum.RawIncidences.difference.{0, 0, 0}
                  (Fin
                    (@List.length.{0} ThreeSum.BandRawA.Label
                      (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
                  (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C))
                  (fun
                      (i :
                        Fin
                          (@List.length.{0} ThreeSum.BandRawA.Label
                            (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs))) =>
                    ThreeSum.BandRawA.valueAt (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs
                      (fun (j : Nat) =>
                        @List.getD.{0} Int A j (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                      (@Fin.val
                        (@List.length.{0} ThreeSum.BandRawA.Label
                          (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs))
                        i))
                  (fun (i : Fin (@List.length.{0} Int B)) =>
                    @List.getD.{0} Int B (@Fin.val (@List.length.{0} Int B) i)
                      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                  (fun (i : Fin (@List.length.{0} Int C)) =>
                    @List.getD.{0} Int C (@Fin.val (@List.length.{0} Int C) i)
                      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                  t))) := by
  sorry
