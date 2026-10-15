-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceBucketScatter_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourceBucketScatter.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:17:31.505982+00:00
-- url     : https://prove2.me/theorems/9c350e7e-9bea-41c8-9438-98e09b82e36b
-- title:
--   Execution of stable original-index bucket scattering
-- statement:
--   Let $c:\mathbb N\to\mathbb N$ have $c(i)<M$ for $i<N$, with key, cursor and flat-index bases $a_k,a_c,a_f$. Suppose memory $\mu$ stores all keys and the initial prefix offsets at the cursors. Assume $a_k+N\le a_c$, $a_c+M\le a_f$, $a_f+N$ fits memory, and addresses fit words. In any Light program containing the scatter body, at depth $d$ it writes
--
--   $$\nu(a_f+\operatorname{position}(c,N,i))=i\quad(i<N),\qquad\nu(a_c+r)=\operatorname{offset}(c,N,r+1)\quad(r<M),$$
--
--   within its specified $N$-dependent time, preserving memory outside $[a_c,a_f+N)$.
--
--   This retains every physical input incidence exactly in its own residue bucket.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBucketScatter.lean#L35-L107

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum_SourceBuckets_position_injective

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBucketScatter
end ThreeSum.LightSourceBucketScatter
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketScatter
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketScatter
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceBucketScatter
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketScatter

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceBucketScatter.meets {pMain : ℕ} (hmain : P[pMain]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketScatter.body)
    {μ : ℕ → ℤ} {keys cursor flat N M : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeys : keys+N ≤ cursor) (hcursor : cursor+M ≤ flat) (hspace : flat+N ≤ lim.space)
    (hkey : ∀ i < N, key i < M)
    (hread : ∀ i < N, μ (keys+i) = (key i : ℤ))
    (hzero : ∀ r < M, μ (cursor+r) = (_root_.ThreeSum.SourceBuckets.offset key N r : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [keys,cursor,flat,N,M] μ (_root_.ThreeSum.LightSourceBucketScatter.time N)
      (fun _ ν => (∀ i < N, ν (flat+_root_.ThreeSum.SourceBuckets.position key N i) = (i : ℤ)) ∧
        (∀ r < M, ν (cursor+r) = (_root_.ThreeSum.SourceBuckets.offset key N (r+1) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν cursor (flat+N-cursor)) := by sorry
