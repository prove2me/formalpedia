-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourcePreparation_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:19:10.586158+00:00
-- url     : https://prove2.me/theorems/84cb85f1-6fb4-4ef1-b7a2-69fce2e7e741
-- title:
--   Preparing raw endpoints and independent source flags
-- statement:
--   Fix $J$ blocks of width $L$, required row size $h\le L$, positive modulus $p$, cap, and $n$ valid masks below $2^{JL}$. Stored occurrence and candidate maps, both coefficient families bounded by $U$, and both histogram families bounded by $V$ satisfy their index and read predicates. Under the specified array separation, scratch, word, helper, and depth bounds, the program writes both flattened-coefficient raw hash arrays and both independent trimming-flag arrays, preserves memory below the coefficient workspace, and meets its stated time.
--
--   This preparation theorem produces the actual endpoint and independent trimming arrays consumed by source-stage construction.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourcePreparation.lean#L44-L149

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean
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
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourceHashes_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceFlagArray_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.LightSourcePreparation
end ThreeSum.LightSourcePreparation
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation
end ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourcePreparation
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.Procs.meets {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR masks n coeff0 coeff1 rawLeft rawRight flags
      bitBase rowOut work U V M K : ℕ}
    (sel candidate mask : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*L+5 ≤ lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*L*M ≤ coeff0)
    (hcandidates : candidates+M ≤ coeff0)
    (hleft : histL+K*p ≤ coeff0) (hright : histR+K*p ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*L ≤ coeff1)
    (hc1 : coeff1+J*L ≤ rawLeft) (hrawLeft : rawLeft+n ≤ rawRight)
    (hrawRight : rawRight+n ≤ flags) (hflags : flags+2*n+2 ≤ bitBase)
    (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : _root_.ThreeSum.LightSourcePreparation.space work J L U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourcePreparation.word J L p U V cap : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M) (hcandidate : ∀ s < M, candidate s < K)
    (hoccRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates+s) = (candidate s : ℤ))
    (hread0 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+L+a) = (w1 s a : ℤ))
    (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U)
    (hcountL : ∀ k < K, ∀ r < p, μ (histL+k*p+r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR+k*p+r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V)
    (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskBound : ∀ i < n, mask i < 2^(J*L)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,masks,n,coeff0,coeff1,rawLeft,rawRight,
        flags,bitBase,rowOut,work]
      μ (_root_.ThreeSum.LightSourcePreparation.time n J L U) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) =
          (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w0) (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w1) (J*L) (mask i) : ℤ)) ∧
        (∀ i < n, ν (rawRight+i) =
          (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w1) (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w0) (J*L) (mask i) : ℤ)) ∧
        (∀ i < n, ν (flags+i) =
          (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ)) ∧
        (∀ i < n, ν (flags+n+i) =
          (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν coeff0) := by sorry
