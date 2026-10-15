-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOriginalOffset_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:26:15.603373+00:00
-- url     : https://prove2.me/theorems/00e5d9f5-064e-4df8-a90d-1089360783eb
-- title:
--   Correct deterministic offset selection from original arrays
-- statement:
--   Let nonzero modulus $p$ and two original integer arrays have lengths at most $N$ and values bounded by $U$. Assume the inputs end before the free address, the concrete offset interface and stated space/word bounds hold, addresses fit words, and depth $d+\lceil\log_2p\rceil+4$ is available. The procedure returns the exact specified deterministic selected offset in its stated time and preserves the original input prefix.
--
--   Implements the balancing choice used before wanted-pair construction. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOriginalOffset.lean#L91-L182

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBalancedOffset_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCapacity_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightResidueHistogram_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightOriginalOffset
end ThreeSum.LightOriginalOffset
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset
end ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightOriginalOffset
open _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightResidueHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open scoped _root_.BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.Procs.meets {pMain a b nLeft nRight p N free U : ℕ} [NeZero p]
    {μ : ℕ → ℤ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nLeft ≤ free) (hb : b+nRight ≤ free)
    (hnLeft : nLeft ≤ N) (hnRight : nRight ≤ N)
    (hspace : _root_.ThreeSum.LightOriginalOffset.space free p N U ≤ lim.space) (hword : (_root_.ThreeSum.LightOriginalOffset.word p N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 p+4 ≤ lim.depth)
    (hLeft : ∀ i < nLeft, |μ (a+i)| ≤ (U : ℤ))
    (hRight : ∀ i < nRight, |μ (b+i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,nLeft,nRight,p,N,free] μ (_root_.ThreeSum.LightOriginalOffset.time p nLeft nRight U)
      (fun r ν => r = (_root_.ThreeSum.LightOriginalOffset.selected p (fun i => μ (a+i)) (fun i => μ (b+i)) nLeft nRight : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by sorry
