-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Compiler_steps_start
-- name    : ThreeSum1960614.Machine.Light.Compiler.steps_start
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:18.308652+00:00
-- url     : https://prove2.me/theorems/b7b94ea4-39b0-440b-8c92-3e53ca2b0216
-- title:
--   Execution of the compiler startup code
-- statement:
--   Let $P$ be a Light program, $p_0\in\mathbb N$ its entry procedure, and $\delta$ its decision/output mode. Assume $-1$ is representable in a $W$-bit word. From any machine memory, the compiled program reaches its main-code position and the specified initialized memory in exactly $$d(P,\delta)+F(P)+9$$ steps, where $d$ is the dispatcher position and $F$ the compiled frame size.
--
--   Accounts for initialization before source-level simulation begins. This is a supporting lemma in the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Compiler/StartUp.lean#L236-L253

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

theorem ThreeSum1960614.Machine.Light.Compiler.steps_start (P : _root_.ThreeSum1960614.Machine.Light.Program) (p0 : ℕ) (dec : Bool) (hneg : _root_.ThreeSumApsp.WordRam.InRange W (-1))
    (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps (_root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec) (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec + _root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P + 9) ⟨0, m⟩
      ⟨_root_.Light.Compiler.mainPos, _root_.Light.Compiler.startMem (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) m⟩ := by sorry
