-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourceBatchStep_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:34:53.007073+00:00
-- url     : https://prove2.me/theorems/186ed644-5d20-4ea2-9a57-8c2fed1b9d85
-- title:
--   Execution of one retained paired-source bank slot
-- statement:
--   Let finite decidable types carry sets B,C with integer maps and bijective physical array enumerations of lengths $N_L,N_R$. Fix $h,J$, cutoff $c\le W=J\cdot464h$, arithmetic modulus $p$, signed shift $\delta$, global output $q$, bank count $N$ and slot $i<N$. Suppose memory stores its exact occurrence row, selected-cover maps/candidate indices/bucket counts and both original-value source histograms modulo the block-source modulus; left uses zero shift and right uses $\delta$. All these retained arrays end before batch base $b$. Assume addresses fit words, the exact retained-host space bound at the computed batch work pointer and word bound for $(N_L,N_R,h,J)$ fit, and depth $d+W+10$ is allowed. With the literal step closure, the program constructs all left/right source-zeta stages in slot $i$, writes their two computed bases at $b+2i,b+2i+1$, meets its stated time, and preserves cells below the slot payload except those two pointer cells.
--
--   This fills one reusable occurrence-indexed source-bank entry from the same original input histograms.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourceBatchStep.lean#L46-L200

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
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
import Mathlib.Data.Fintype.Fin
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

namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.Procs
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.Procs


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.LightBlockSourceBatchStep
end ThreeSum.LightBlockSourceBatchStep
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.Procs.meets {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.Procs P pMain)
    {μ : ℕ → ℤ} {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR
      base count i : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ A)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(464*h)+10 ≤ lim.depth)
    (hcut : cut ≤ J*(464*h)) (hi : i < count)
    (hocc : occ+J ≤ base) (hmaps : maps+2*(464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ base)
    (hcandidates : candidates+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ base)
    (hleft : histL+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ base)
    (hright : histR+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ base)
    (hsourceHistL : sourceHistL+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ base)
    (hsourceHistR : sourceHistR+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ base)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space (_root_.ThreeSum.LightBlockSourceBatchLayout.work base count (J*(464*h)) cut) h J ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word NL NR h J : ℤ) ≤ lim.word)
    (hinputL : ∀ j : Fin NL, vL j.val = b (eL j))
    (hinputR : ∀ j : Fin NR, vR j.val = a (eR j))
    (hhistReadL : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
      μ (sourceHistL+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 vL NL r : ℤ))
    (hhistReadR : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
      μ (sourceHistR+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift vR NR r : ℤ))
    (hoccRead : ∀ j < J, μ (occ+j) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) j : ℤ))
    (hcover : _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,cut,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,occ,maps,candidates,
        histL,histR,sourceHistL,sourceHistR,base,_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,count,
        _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count,_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut,
        _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base count (J*(464*h)) cut,_root_.ThreeSum.LightBlockSourceBatchLayout.bitBase base count (J*(464*h)) cut,
        _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut base count (J*(464*h)) cut,_root_.ThreeSum.LightBlockSourceBatchLayout.work base count (J*(464*h)) cut,i]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.time h J cut) (fun _ ν =>
        _root_.ThreeSum.LightZetaStages.StoredThrough ν (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count (J*(464*h)) cut i) cut
          (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource (p : ℤ) B b q) (J*(464*h)) ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough ν (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count (J*(464*h)) cut i) cut
          (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource (p : ℤ) shift A a q) (J*(464*h)) ∧
        ν (base+2*i) = (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count (J*(464*h)) cut i : ℤ) ∧
        ν (base+2*i+1) = (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count (J*(464*h)) cut i : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum.LightBlockSourceBatchLayout.slot base count (J*(464*h)) cut i) (base+2*i) 2) := by sorry
