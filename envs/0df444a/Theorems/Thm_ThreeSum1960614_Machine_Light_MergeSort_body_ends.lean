-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_MergeSort_body_ends
-- name    : ThreeSum1960614.Machine.Light.MergeSort.body_ends
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:45.775373+00:00
-- url     : https://prove2.me/theorems/3d6ebf0b-d6af-49eb-8539-3f6ade23fbb3
-- title:
--   One merge-sort body meets its exact sorting contract
-- statement:
--   Suppose sort, half, merge, and copy helpers are installed. Let integer list $L$ be stored before reusable scratch, with enough space and word-sized addresses. Assume one call level and an induction contract for every recursive sublist whose doubled length is at most $|L|+1$. The sort body, begun with the length, source, and scratch frame, establishes the full sorted-output predicate within $\operatorname{sortTime}(|L|)$.
--
--   This body theorem is the induction step behind the verified merge sort reused by normalization and catalog indexing.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L152-L197

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
import Theorems.Thm_Light_MergeSort_clog_split
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_ThreeSum1960614_Machine_Light_half_meets
import Theorems.Thm_ThreeSum1960614_Machine_Light_merge_meets

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

theorem ThreeSum1960614.Machine.Light.MergeSort.body_ends (C : _root_.ThreeSum1960614.Machine.Light.MergeSort.Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) {d a fr : ℕ} {L : List ℤ}
    {μ : ℕ → ℤ} (hseg : _root_.ThreeSum1960614.Machine.Light.Seg μ a L) (haf : a + L.length ≤ fr) (hfr : fr + L.length ≤ lim.space)
    (hd : d < lim.depth)
    (ih : ∀ (a' : ℕ) (L' : List ℤ) (μ' : ℕ → ℤ), 1 < L.length → 2 * L'.length ≤ L.length + 1 →
      _root_.ThreeSum1960614.Machine.Light.Seg μ' a' L' → a' + L'.length ≤ fr →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pSort (d + 1) [L'.length, a', fr] μ' (_root_.Light.sortTime L'.length) fun _ =>
        _root_.ThreeSum1960614.Machine.Light.MergeSort.Sorted μ' a' fr L') :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.sortBody pSort pHalf pMerge pCopy) ⟨_root_.Light.frame [L.length, a, fr], μ⟩
      (_root_.Light.sortTime L.length) fun σ' => _root_.ThreeSum1960614.Machine.Light.MergeSort.Sorted μ a fr L σ'.mem := by sorry
