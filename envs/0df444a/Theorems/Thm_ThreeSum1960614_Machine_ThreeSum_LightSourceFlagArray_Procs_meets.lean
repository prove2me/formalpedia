-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceFlagArray_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:09:49.504395+00:00
-- url     : https://prove2.me/theorems/26a00539-1137-422c-b296-89dcf7a28e49
-- title:
--   Building both complete independent flag arrays
-- statement:
--   Let $n$ stored global masks lie below $2^{JL}$, with valid selected occurrence and candidate indices, coefficient rows bounded by $U$, independent histograms bounded by $V$, $p>0$, and $h\le L$. Assume the concrete procedure interface, input arrays before the paired output, ordered bit/row/arithmetic scratch, and the stated space, word, address, and depth bounds. The routine writes the exact left and right global flag for every mask in adjacent arrays within its stated time, preserving other cells below bit scratch.
--
--   Makes every endpoint's independent trimming decision available as actual stored data. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceFlagArray.lean#L56-L187

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceMaskFlags_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSourceFlagArray
end ThreeSum.LightSourceFlagArray
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray
end ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray
namespace ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
end ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceFlagArray
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work U V M K : ℕ}
    (sel candidate mask : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*L+4 ≤ lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ dst) (hmaps : maps+2*L*M ≤ dst)
    (hcandidates : candidates+M ≤ dst)
    (hleft : histL+K*p ≤ dst) (hright : histR+K*p ≤ dst)
    (hmasks : masks+n ≤ dst) (hdst : dst+2*n+2 ≤ bitBase)
    (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : _root_.ThreeSum.LightSourceMaskFlags.space work J L U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourceMaskFlags.word J L p U V cap : ℤ) ≤ lim.word)
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
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,masks,n,dst,bitBase,rowOut,work]
      μ (_root_.ThreeSum.LightSourceFlagArray.time n J L U) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ)) ∧
        (∀ i < n, ν (dst+n+i) = (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν bitBase dst (2*n+2)) := by sorry
