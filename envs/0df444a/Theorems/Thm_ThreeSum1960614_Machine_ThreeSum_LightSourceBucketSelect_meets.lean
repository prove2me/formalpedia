-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceBucketSelect_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:51:20.225068+00:00
-- url     : https://prove2.me/theorems/2b09f47b-5921-4236-9970-2d29d64b2c7b
-- title:
--   Constant-time independent-flag-aware bucket selection
-- statement:
--   Let a Light program contain the bucket-selection body at procedure $p_0$, and let $\mu$ store contiguous original-index buckets for a code map $c:\mathbb N\to\mathbb N$, $N$ indices, $M$ residues, prefix offsets at $a_o$, and flat indices at $a_f$. Let $r<M$, $\phi\le1$ be a natural flag, and $b$ the two-cell destination. Assume all $c(i)<M$ for $i<N$, both stored arrays end no later than $b$, $b+2$ fits memory, and addresses fit words. At any depth $d$, the call takes at most $120$ steps and writes
--
--   $$\nu(b)=a_f+\operatorname{offset}(c,N,r),\qquad\nu(b+1)=\begin{cases}|\{i<N:c(i)=r\}|,&\phi=1,\\0,&\phi=0.\end{cases}$$
--
--   Every other memory cell is unchanged.
--
--   This makes independent trimming flags control the exact original-index fiber scanned by terminal tests.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBucketSelect.lean#L51-L99

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

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect.meets {pMain : ℕ} (hmain : P[pMain]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect.body)
    {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r flag dst : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat)
    (hw : (lim.space : ℤ) ≤ lim.word) (hoffsets : offsets+M+1 ≤ dst)
    (hflat : flat+N ≤ dst) (hspace : dst+2 ≤ lim.space)
    (hkey : ∀ i < N, key i < M) (hr : r < M) (_hflag : flag ≤ 1) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [offsets,flat,r,flag,dst,M,N] μ 120
      (fun _ ν => ν dst = ((flat+_root_.ThreeSum.SourceBuckets.offset key N r : ℕ) : ℤ) ∧
        ν (dst+1) = (_root_.ThreeSum.LightSourceBucketSelect.countSelected key N r flag : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst 2) := by sorry
