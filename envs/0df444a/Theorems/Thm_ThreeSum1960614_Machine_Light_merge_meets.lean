-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_merge_meets
-- name    : ThreeSum1960614.Machine.Light.merge_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:28:56.385096+00:00
-- url     : https://prove2.me/theorems/38412585-6484-46a6-ace8-bd28a1a6df1d
-- title:
--   Merging two stored sorted arrays
-- statement:
--   Suppose the merge precondition holds for limits $L$, initial memory $\mu$, source bases $a,b$, destination $o$, and integer lists $l,r$, and the merge body is installed. The call writes $l.\operatorname{merge}(r)$ at $o$ within the merge time for $|l|+|r|$, changing only that destination window.
--
--   This merge contract supplies the stable sorted-array step required by normalization and packed catalog indexing.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L155-L194

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_of_blockSafe
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons

namespace Light
end Light
namespace Light.Merge
end Light.Merge
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Merge
end ThreeSum1960614.Machine.Light.Merge

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
open _root_.Light.Merge
open _root_.ThreeSum1960614.Machine.Light.Merge

variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}

theorem ThreeSum1960614.Machine.Light.merge_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.mergeBody)
    (C : _root_.ThreeSum1960614.Machine.Light.Merge.Pre lim μ a b dst l r) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [a, l.length, b, r.length, dst] μ (_root_.Light.mergeTime (l.length + r.length)) fun _ μ' =>
      _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (l.merge r) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (l.length + r.length) := by sorry
