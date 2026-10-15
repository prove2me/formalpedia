-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingTerminalPreparation_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:35:48.161675+00:00
-- url     : https://prove2.me/theorems/d7a259df-0013-4023-b771-63481fc9f241
-- title:
--   Preparing terminal endpoint and trimming arrays
-- statement:
--   For occurrence family $o$ in $J$ width-$464h$ blocks, let two stored mask arrays encode $n$ coordinate subsets. Assume exact occurrence indices, retained cover input, ordered destination and scratch regions, and the prescribed source-preparation word, space, and depth bounds. Procedure 17 writes the semantic left and right endpoints and the separate indicator flags for left and right admissibility. It returns the exact stop address, preserves memory below the output base, and meets the stated preparation time.
--
--   This preparation contract translates retained prefix masks into original endpoints and independent terminal trimming flags.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingTerminalPreparation.lean#L52-L140

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

namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation


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
namespace ThreeSum.LightReportingTerminalPreparation
end ThreeSum.LightReportingTerminalPreparation
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
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingTerminalPreparation
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation

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
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
set_option maxHeartbeats 2600000
set_option maxRecDepth 12000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation.program_meets {μ : ℕ→ℤ}
    {h J occ maps candidates histL histR masksL masksR n base bitBase rowOut work d : ℕ}
    (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (setsL setsR : ℕ→Finset (_root_.ThreeSum.BlockRows.Coord J (464*h)))
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+J*(464*h)+6≤lim.depth)
    (hocc : occ+J≤base) (hmaps : maps+2*(464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h≤base)
    (hcandidates : candidates+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h≤base)
    (hleft : histL+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h≤base)
    (hright : histR+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h≤base)
    (hmasksL : masksL+n≤base) (hmasksR : masksR+n≤base)
    (hstop : _root_.ThreeSum.LightReportingTerminalPreparation.stop base (J*(464*h)) n≤bitBase)
    (hbits : bitBase+J*(464*h)≤rowOut) (hrowOut : rowOut+2≤work)
    (hspace : _root_.ThreeSum.LightSourcePreparation.space work J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)≤lim.space)
    (hword : (_root_.ThreeSum.LightSourcePreparation.word J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
      ((464*h).choose h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) : ℤ)≤lim.word)
    (hoccRead : ∀ j<J, μ (occ+j)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o j : ℤ))
    (hcover : _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR)
    (hmaskL : ∀ i<n, μ (masksL+i)=(_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (setsL i)) : ℤ))
    (hmaskR : ∀ i<n, μ (masksR+i)=(_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (setsR i)) : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation.program 17 d
      [J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,occ,maps,candidates,histL,histR,masksL,masksR,n,base,bitBase,rowOut,work]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation.time h J n) (fun r ν => r=(_root_.ThreeSum.LightReportingTerminalPreparation.stop base (J*(464*h)) n : ℤ) ∧
        (∀ i<n, ν (_root_.ThreeSum.LightReportingTerminalPreparation.leftRaw base (J*(464*h))+i)=_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft o (setsL i)) ∧
        (∀ i<n, ν (_root_.ThreeSum.LightReportingTerminalPreparation.rightRaw base (J*(464*h)) n+i)=_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o (setsR i)) ∧
        (∀ i<n, ν (_root_.ThreeSum.LightReportingTerminalPreparation.leftFlags base (J*(464*h)) n+i)=(if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed o (setsL i) then 1 else 0 : ℕ)) ∧
        (∀ i<n, ν (_root_.ThreeSum.LightReportingTerminalPreparation.rightFlags base (J*(464*h)) n+i)=(if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o (setsR i) then 1 else 0 : ℕ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν base) := by sorry
