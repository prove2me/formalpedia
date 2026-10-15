-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Exec_bounded
-- name    : ThreeSum1960614.Machine.Light.Exec.bounded
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:27.100651+00:00
-- url     : https://prove2.me/theorems/6110b732-4139-4fb8-9c24-3ef496852d0d
-- title:
--   Execution preserves bounded states
-- statement:
--   For limits $L$, program $P$, and depth $d$, any execution of statement $s$ from $\sigma$ to $\sigma'$ in $c$ steps preserves the bounded-state predicate: boundedness of $\sigma$ implies boundedness of $\sigma'$.
--
--   This invariant ensures each light execution remains compatible with the finite machine word and address limits.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/RunsStayInLimits.lean#L65-L79

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Tactic.SplitIfs

namespace Light
end Light
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.Light.Exec.bounded {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ} (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c)
    (hσ : σ.Bounded lim) : σ'.Bounded lim := by sorry
