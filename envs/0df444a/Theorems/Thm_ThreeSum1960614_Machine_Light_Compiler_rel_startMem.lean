-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Compiler_rel_startMem
-- name    : ThreeSum1960614.Machine.Light.Compiler.rel_startMem
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:23.963798+00:00
-- url     : https://prove2.me/theorems/effbf234-25cc-4887-9a99-cd54c4b44249
-- title:
--   Initialized memory represents the initial Light frame
-- statement:
--   Let compiler size data $Z$ have frame width at least $3$ and a dispatcher pool containing twice the main-frame index. Suppose the initial machine memory encodes a Light memory $\mu$ at all allowed nonnegative addresses and the two argument cells contain the encodings of integers $i,j$. Then the compiler startup memory represents the main Light frame $[0,i,j]$ with memory $\mu$.
--
--   Establishes the initial simulation relation after startup. This is a supporting lemma in the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Compiler/StartUp.lean#L193-L223

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
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
namespace Light.Compiler
end Light.Compiler
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

open _root_.Light.Compiler
open _root_.ThreeSum1960614.Machine.Light.Compiler

variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}

theorem ThreeSum1960614.Machine.Light.Compiler.rel_startMem (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) (h3 : 3 ≤ Z.F) (hpool : 2 * _root_.Light.Compiler.mainFrame ≤ Z.disp) {μ : ℕ → ℤ}
    {i j : ℤ} (hm : ∀ a < Z.lim.space, m (a : ℤ) = _root_.ThreeSumApsp.WordRam.wd W (μ a)) (hi : m _root_.Light.Compiler.cARG1 = _root_.ThreeSumApsp.WordRam.wd W i)
    (hj : m _root_.Light.Compiler.cARG2 = _root_.ThreeSumApsp.WordRam.wd W j) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z ⟨_root_.Light.frame [0, i, j], μ⟩ _root_.Light.Compiler.mainFrame (_root_.Light.Compiler.startMem Z.F Z.disp m) := by sorry
