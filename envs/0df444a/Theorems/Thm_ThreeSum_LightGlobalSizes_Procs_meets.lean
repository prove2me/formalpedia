-- Prove2me | Theorems.Thm_ThreeSum_LightGlobalSizes_Procs_meets
-- name    : ThreeSum.LightGlobalSizes.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:35:10.42788+00:00
-- url     : https://prove2.me/theorems/8d4a7926-2d3b-4474-a164-6930f885b7a1
-- title:
--   Verified computation of global powers and rounded band parameters
-- statement:
--   Let $C,p\ge1$ and $J,m,z\in\mathbb N$. Define $e=\lfloor m/20\rfloor$, $D_0=2^e$, $R=\lceil\sqrt{C^J}\rceil$, and $g=\lceil R/D_0\rceil$. Suppose $P$ contains the global-size constructor with its natural-power, small-division, and integer-square-root procedures. For machine limits $S,W,D$, assume $z+5\le S\le W$, $d<D$, and $1000(C+p+J+m+C^J+p^J+D_0+1)\le W$. From any integer memory $\mu$, execution on $(C,p,J,m,z)$ finishes within $40J+40e+20g+18(R-1)+452$ steps and satisfies
--
--   $$
--   r=p^J,\qquad \mu'[z:z+5]=[C^J,p^J,R,D_0,g].
--   $$
--
--   Memory outside these five cells is unchanged. This initializes the actual global radix and rounded band size from local parameters.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightGlobalSizes.lean#L63-L151

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
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
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_Light_sqrt_meets
import Theorems.Thm_ThreeSum_LightNatPower_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightGlobalSizes.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightGlobalSizes.Procs P pMain) {μ : Nat → Int}
  {C p J mu dst : Nat} (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hC : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) C)
  (hp : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) p)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightGlobalSizes.word C p J mu)) lim.word),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt C)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt mu)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int))))))
    μ (ThreeSum.LightGlobalSizes.time C J mu) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p J)))
      (And (Light.Seg μ' dst (ThreeSum.LightGlobalSizes.values C p J mu))
        (Light.SameOutside μ μ' dst (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) := by
  sorry
