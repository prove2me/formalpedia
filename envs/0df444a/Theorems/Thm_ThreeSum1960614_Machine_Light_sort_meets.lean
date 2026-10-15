-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_sort_meets
-- name    : ThreeSum1960614.Machine.Light.sort_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:52:54.772986+00:00
-- url     : https://prove2.me/theorems/b65c72b9-4f19-4113-abc4-ba11f0d3d541
-- title:
--   Correctness and cost of merge sort
-- statement:
--   Let the concrete sort, half, merge, and copy bodies be present. Suppose a list $L$ is stored at $a$, the input ends before scratch $f$, scratch has $|L|$ cells, addresses and $1$ fit words, and $d+\lceil\log_2|L|\rceil+1$ fits call depth. The sort procedure runs within its specified sort time and leaves a sorted permutation of $L$ at $a$, preserving all cells below $f$ except the input segment.
--
--   Provides the original upstream sorting component used in normalization and catalog lookup. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L199-L217

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_MergeSort_body_ends

namespace Light
end Light
namespace Light.MergeSort
end Light.MergeSort
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.MergeSort
end ThreeSum1960614.Machine.Light.MergeSort

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
open _root_.Light.MergeSort
open _root_.ThreeSum1960614.Machine.Light.MergeSort

variable {pSort pHalf pMerge pCopy : ℕ}

theorem ThreeSum1960614.Machine.Light.sort_meets (C : _root_.ThreeSum1960614.Machine.Light.MergeSort.Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) {a fr : ℕ} {L : List ℤ} {μ : ℕ → ℤ}
    (hseg : _root_.ThreeSum1960614.Machine.Light.Seg μ a L) (haf : a + L.length ≤ fr) (hfr : fr + L.length ≤ lim.space) :
    ∀ d, d + Nat.clog 2 L.length + 1 ≤ lim.depth →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pSort d [L.length, a, fr] μ (_root_.Light.sortTime L.length) fun _ => _root_.ThreeSum1960614.Machine.Light.MergeSort.Sorted μ a fr L := by sorry
