-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourcePreparation_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:28:24.829816+00:00
-- url     : https://prove2.me/theorems/397af7ee-003b-4843-8b6a-b84c67e5cc5d
-- title:
--   Execution of endpoint hashes and independent trim flags
-- statement:
--   Let $h,J,n\in\mathbb N$, occurrence vector $o$, and block-coordinate subsets $S_i$ for $i<n$ be given. Suppose memory $\mu$ stores the exact occurrence indices, original selected coefficient rows, occurrence-to-candidate indices, candidate left/right bucket counts and indexed masks of $S_i$. All retained arrays end before the first gathered coefficient row. Reserve in order two length-$J\cdot464h$ coefficient rows, two length-$n$ raw-hash arrays, two flag rows plus two cells, a width-sized bit row, two row-output cells, and scratch. Assume these reservations do not overlap in that order, addresses fit words, the exact preparation space/word budgets fit and $d+J\cdot464h+5$ is allowed. With the literal procedure closure present, the call writes both positional endpoint hashes and
--
--   $$\phi_L(i)=\mathbf1_{\mathrm{LeftAllowed}(o,S_i)},\qquad\phi_R(i)=\mathbf1_{\mathrm{RightAllowed}(o,S_i)},$$
--
--   within its stated time, preserving all memory below the gathered coefficient base.
--
--   This constructs original-encoding endpoints and independent trimming decisions from actual retained maps and histograms.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourcePreparation.lean#L20-L89

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
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
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
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
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.Data.List.Range
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockIndex_maskHash_left
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockIndex_maskHash_right
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverSchedule_indices_lt
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverSchedule_indices_map
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourcePreparation_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LocalMaskHashes_indexed_bucket_count
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_maskOf
import Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.LightBlockSourcePreparation
end ThreeSum.LightBlockSourcePreparation
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
end ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.BlockSourceFlags
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
set_option maxHeartbeats 1700000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation.meets {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.Procs P pMain)
    {μ : ℕ → ℤ} {h J occ maps candidates histL histR masks n coeff0 coeff1 rawLeft rawRight flags
      bitBase rowOut work : ℕ}
    (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (sets : ℕ → Finset (_root_.ThreeSum.BlockRows.Coord J (464*h)))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(464*h)+5 ≤ lim.depth)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*(464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ coeff0)
    (hcandidates : candidates+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ coeff0)
    (hleft : histL+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ coeff0)
    (hright : histR+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*(464*h) ≤ coeff1)
    (hc1 : coeff1+J*(464*h) ≤ rawLeft) (hrawLeft : rawLeft+n ≤ rawRight)
    (hrawRight : rawRight+n ≤ flags) (hflags : flags+2*n+2 ≤ bitBase)
    (hbits : bitBase+J*(464*h) ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : _root_.ThreeSum.LightSourcePreparation.space work J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourcePreparation.word J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
      ((464*h).choose h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) : ℤ) ≤ lim.word)
    (hoccRead : ∀ j < J, μ (occ+j) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o j : ℤ))
    (hcandidateRead : ∀ s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h,
      μ (candidates+s.val) = (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s : ℤ))
    (hread0 : ∀ s < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, ∀ a < 464*h,
      μ (maps+2*(464*h)*s+a) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false s a : ℤ))
    (hread1 : ∀ s < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, ∀ a < 464*h,
      μ (maps+2*(464*h)*s+464*h+a) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true s a : ℤ))
    (hcountL : ∀ k < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h, ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,
      μ (histL+k*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+r) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.leftCount h k r : ℤ))
    (hcountR : ∀ k < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h, ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,
      μ (histR+k*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+r) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.rightCount h k r : ℤ))
    (hmaskRead : ∀ i < n,
      μ (masks+i) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (sets i)) : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,occ,maps,candidates,histL,histR,masks,n,
        coeff0,coeff1,rawLeft,rawRight,flags,bitBase,rowOut,work]
      μ (_root_.ThreeSum.LightSourcePreparation.time n J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft o (sets i)) ∧
        (∀ i < n, ν (rawRight+i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o (sets i)) ∧
        (∀ i < n, ν (flags+i) = (if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed o (sets i) then 1 else 0 : ℕ)) ∧
        (∀ i < n, ν (flags+n+i) = (if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o (sets i) then 1 else 0 : ℕ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν coeff0) := by sorry
