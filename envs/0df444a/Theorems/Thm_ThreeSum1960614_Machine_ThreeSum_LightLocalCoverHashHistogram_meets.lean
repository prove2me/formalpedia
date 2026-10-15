-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverHashHistogram_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:40:45.213797+00:00
-- url     : https://prove2.me/theorems/bf6f2939-9fbf-492f-a97e-234534810ec6
-- title:
--   Constructing exact local hash codes and histogram counts
-- statement:
--   Let $n$ stored width-$L$ masks be valid, and let two stored coefficient arrays be bounded by $U$. For positive modulus $p$, assume the ordered raw-hash, code, histogram, and scratch regions, helper placement, finite space and word bounds, and depth $d+L+2$. The program writes every exact reduced mask code and its physical multiplicity histogram, preserves inputs and the specified unrelated cells, and meets the declared time.
--
--   This histogram theorem identifies the concrete local hash buckets with their exact physical vertex multiplicities.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalCoverHashHistogram.lean#L21-L96

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightHistogram_histogram_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskHashes_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightResidues_residues_ends
import Theorems.Thm_ThreeSum_OneHotMask_eval_le

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHashHistogram
end ThreeSum.LightHashHistogram
namespace ThreeSum.LightLocalCoverHashHistogram
end ThreeSum.LightLocalCoverHashHistogram
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHashHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHashHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightLocalCoverHashHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightHashHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHashHistogram
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightHashHistogram.Procs P pMain)
    {μ : ℕ → ℤ} {L masks raw codes hist n src0 src1 p work U : ℕ}
    (mask w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+2 ≤ lim.depth)
    (hp : 0 < p) (hspace : _root_.ThreeSum.LightHashHistogram.space work L U ≤ lim.space)
    (hmasks : masks+n ≤ raw) (hsrc0 : src0+L ≤ raw) (hsrc1 : src1+L ≤ raw)
    (hraw : raw+n ≤ codes) (hcodes : codes+n ≤ hist) (hhist : hist+p ≤ work)
    (hword : (_root_.ThreeSum.LightHashHistogram.word L p U : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,masks,raw,codes,hist,n,src0,src1,p,work] μ (_root_.ThreeSum.LightHashHistogram.time L n p U)
      (fun _ μ' =>
        (∀ i < n, μ' (codes+i) = (_root_.ThreeSum.LightHashHistogram.code L p mask w0 w1 i : ℤ)) ∧
        (∀ r < p, μ' (hist+r) = (_root_.ThreeSum.LightHistogram.count (_root_.ThreeSum.LightHashHistogram.code L p mask w0 w1) r n : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ μ' raw ∧ _root_.ThreeSum.LightLocalCoverHashHistogram.Preserved μ μ' work raw codes hist n p) := by sorry
