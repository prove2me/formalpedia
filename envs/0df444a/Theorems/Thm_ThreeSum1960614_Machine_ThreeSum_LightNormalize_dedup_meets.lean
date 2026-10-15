-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNormalize_dedup_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedup_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:47:06.426982+00:00
-- url     : https://prove2.me/theorems/5941fb5c-458a-4f0e-a250-8e1d9b4c6e35
-- title:
--   Deduplicating a sorted physical array
-- statement:
--   Let a nondecreasing integer list $L$ be stored at source $s$. Suppose the deduplication body is installed, source and destination are disjoint in order, the destination extent fits memory, addresses fit words, and depth $d+|L|$ is allowed. The call writes $L.\operatorname{dedup}$, returns its length within the deduplication-time bound, and changes only the reserved destination window.
--
--   This deduplication contract produces distinct normalized values while preserving their original value membership.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightNormalize.lean#L52-L123

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
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
import Theorems.Thm_Light_seg_cons

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightNormalize
end ThreeSum.LightNormalize
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightNormalize
end ThreeSum1960614.Machine.ThreeSum.LightNormalize

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightNormalize
open _root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedup_meets {pDedup : ℕ}
    (hprog : P[pDedup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedupBody pDedup))
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) :
    ∀ (L : List ℤ) (μ : ℕ → ℤ) (src dst d : ℕ),
      L.Pairwise (· ≤ ·) → _root_.ThreeSum1960614.Machine.Light.Seg μ src L → src+L.length ≤ dst →
      dst+L.length ≤ lim.space → d+L.length ≤ lim.depth →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pDedup d [src,L.length,dst] μ (_root_.ThreeSum.LightNormalize.dedupTime L.length)
        (fun r μ' => r = (L.dedup.length : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ' dst L.dedup ∧
          _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst L.length) := by sorry
