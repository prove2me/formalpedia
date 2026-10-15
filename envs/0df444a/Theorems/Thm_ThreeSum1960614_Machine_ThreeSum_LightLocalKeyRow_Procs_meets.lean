-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalKeyRow_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightLocalKeyRow.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:09:01.204979+00:00
-- url     : https://prove2.me/theorems/6f31c337-6aa0-41bb-a934-326bcf57b888
-- title:
--   Execution of one signed local-key row
-- statement:
--   Let $\lambda,P,d,\mu$ be Light limits, program, depth and memory. A literal procedure-closure record identifies the local-key wrapper and all its callees. Fix width $L$, $n$ masks $m_i<2^L$, coefficient maps $w_F,w_T:\mathbb N\to\mathbb N$ bounded by $U$, their correctly stored rows and mask list, and free base $f$ after all three arrays. Suppose addresses fit words, the explicit local-key word and space budgets fit, and $d+L+2$ is allowed. The call returns $f+L$ and writes
--
--   $$\nu(f+L+i)=E(w_T,0,L,m_i)-E(w_F,0,L,m_i)\quad(i<n),$$
--
--   where $E(u,v,L,m)$ sums $v_j$ at set bits and $u_j$ at unset bits. It meets its specified time and preserves every cell below $f$.
--
--   This realizes the signed local-key list in the same physical mask order as the global encoding.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalKeyRow.lean#L50-L139

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightArray_linear_bounded_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskHashes_meets
import Theorems.Thm_ThreeSum_OneHotMask_eval_le

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLocalKeyRow
end ThreeSum.LightLocalKeyRow
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalKeyRow
end ThreeSum1960614.Machine.ThreeSum.LightLocalKeyRow
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightLocalKeyRow
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalKeyRow

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightLocalKeyRow.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalKeyRow.Procs P pMain)
    {μ : ℕ → ℤ} {L masks n srcFalse srcTrue free U : ℕ}
    (mask wFalse wTrue : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+2 ≤ lim.depth)
    (hspace : _root_.ThreeSum.LightLocalKeyRow.space free L n ≤ lim.space)
    (hmasks : masks+n ≤ free) (hfalse : srcFalse+L ≤ free) (htrue : srcTrue+L ≤ free)
    (hword : (_root_.ThreeSum.LightLocalKeyRow.word L U : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hreadFalse : ∀ i < L, μ (srcFalse+i) = (wFalse i : ℤ))
    (hreadTrue : ∀ i < L, μ (srcTrue+i) = (wTrue i : ℤ))
    (hboundFalse : ∀ i < L, wFalse i ≤ U) (hboundTrue : ∀ i < L, wTrue i ≤ U) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,masks,n,srcFalse,srcTrue,free] μ (_root_.ThreeSum.LightLocalKeyRow.time L n)
      (fun r ν => r=((free+L : ℕ) : ℤ) ∧
        (∀ i < n, ν (free+L+i) =
          (_root_.ThreeSum.OneHotMask.eval wTrue (fun _ => 0) L (mask i) : ℤ)-
          (_root_.ThreeSum.OneHotMask.eval wFalse (fun _ => 0) L (mask i) : ℤ)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by sorry
